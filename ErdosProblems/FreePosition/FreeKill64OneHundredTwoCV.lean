import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwoCVFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwoCVFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwoCVFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwoCVFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwoCVFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwoCVFastPow a n * oneHundredTwoCVFastPow a n * a else oneHundredTwoCVFastPow a n * oneHundredTwoCVFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwoCV_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwoCV_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwoCV_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwoCV_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwoCV_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwoCV_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwoCV_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwoCV_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwoCV_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwoCV_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwoCV_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwoCV_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwoCV_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwoCV_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwoCV_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwoCV_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwoCV_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwoCV_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwoCV_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwoCV_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwoCV_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwoCV_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwoCV_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwoCV_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwoCV_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwoCV_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwoCV_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwoCV_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwoCV_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwoCV_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwoCV_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwoCV_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwoCV_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwoCV_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwoCV_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwoCV_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwoCV_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwoCV_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwoCV_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwoCV_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwoCV_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwoCV_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwoCV_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwoCV_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwoCV_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwoCV_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwoCV_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwoCV_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwoCV_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwoCV_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwoCV_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwoCV_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwoCV_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwoCV_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwoCV_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwoCV_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwoCV_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwoCV_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwoCV_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwoCV_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwoCV_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwoCV_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwoCV_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwoCV_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwoCV_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwoCV_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwoCV_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwoCV_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredTwoCV_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredTwoCV_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwoCV_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTwoCV_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwoCV_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredTwoCV_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwoCV_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTwoCV_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredTwoCV_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredTwoCV_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTwoCV_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredTwoCV_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwoCV_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTwoCV_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTwoCV_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredTwoCV_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredTwoCV_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwoCV_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredTwoCV_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredTwoCV_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwoCV_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwoCV_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredTwoCV_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwoCV_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredTwoCV_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTwoCV_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwoCV_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredTwoCV_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredTwoCV_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredTwoCV_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredTwoCV_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredTwoCV_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredTwoCV_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredTwoCV_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredTwoCV_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredTwoCV_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredTwoCV_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredTwoCV_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredTwoCV_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTwoCV_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredTwoCV_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredTwoCV_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredTwoCV_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwoCV_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredTwoCV_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwoCV_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredTwoCV_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredTwoCV_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredTwoCV_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredTwoCV_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwoCV_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredTwoCV_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredTwoCV_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredTwoCV_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredTwoCV_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredTwoCV_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredTwoCV_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredTwoCV_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredTwoCV_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredTwoCV_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTwoCV_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredTwoCV_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredTwoCV_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredTwoCV_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredTwoCV_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredTwoCV_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredTwoCV_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredTwoCV_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredTwoCV_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredTwoCV_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwoCV_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredTwoCV_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredTwoCV_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredTwoCV_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredTwoCV_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_oneHundredTwoCV_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredTwoCV_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredTwoCV_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredTwoCV_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_oneHundredTwoCV_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredTwoCV_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_oneHundredTwoCV_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredTwoCV_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredTwoCV_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_oneHundredTwoCV_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredTwoCV_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredTwoCV_3251 : Nat.Prime 3251 := by norm_num

private theorem prime_oneHundredTwoCV_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredTwoCV_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredTwoCV_3373 : Nat.Prime 3373 := by norm_num

private theorem prime_oneHundredTwoCV_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredTwoCV_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredTwoCV_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_oneHundredTwoCV_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredTwoCV_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_oneHundredTwoCV_3533 : Nat.Prime 3533 := by norm_num

private theorem prime_oneHundredTwoCV_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredTwoCV_3631 : Nat.Prime 3631 := by norm_num

private theorem prime_oneHundredTwoCV_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredTwoCV_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredTwoCV_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_oneHundredTwoCV_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredTwoCV_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_oneHundredTwoCV_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredTwoCV_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_oneHundredTwoCV_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_oneHundredTwoCV_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_oneHundredTwoCV_4261 : Nat.Prime 4261 := by norm_num

private theorem prime_oneHundredTwoCV_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_oneHundredTwoCV_4561 : Nat.Prime 4561 := by norm_num

private theorem prime_oneHundredTwoCV_4583 : Nat.Prime 4583 := by norm_num

private theorem prime_oneHundredTwoCV_4931 : Nat.Prime 4931 := by norm_num

private theorem prime_oneHundredTwoCV_5011 : Nat.Prime 5011 := by norm_num

private theorem prime_oneHundredTwoCV_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_oneHundredTwoCV_5297 : Nat.Prime 5297 := by norm_num

private theorem prime_oneHundredTwoCV_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredTwoCV_5449 : Nat.Prime 5449 := by norm_num

private theorem prime_oneHundredTwoCV_5641 : Nat.Prime 5641 := by norm_num

private theorem prime_oneHundredTwoCV_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_oneHundredTwoCV_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_oneHundredTwoCV_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredTwoCV_6599 : Nat.Prime 6599 := by norm_num

private theorem prime_oneHundredTwoCV_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_oneHundredTwoCV_6779 : Nat.Prime 6779 := by norm_num

private theorem prime_oneHundredTwoCV_6793 : Nat.Prime 6793 := by norm_num

private theorem prime_oneHundredTwoCV_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_oneHundredTwoCV_8123 : Nat.Prime 8123 := by norm_num

private theorem prime_oneHundredTwoCV_8233 : Nat.Prime 8233 := by norm_num

private theorem prime_oneHundredTwoCV_8467 : Nat.Prime 8467 := by norm_num

private theorem prime_oneHundredTwoCV_9391 : Nat.Prime 9391 := by norm_num

private theorem prime_oneHundredTwoCV_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_oneHundredTwoCV_9491 : Nat.Prime 9491 := by norm_num

private theorem prime_oneHundredTwoCV_9631 : Nat.Prime 9631 := by norm_num

private theorem prime_oneHundredTwoCV_9743 : Nat.Prime 9743 := by norm_num

private theorem prime_oneHundredTwoCV_10141 : Nat.Prime 10141 := by norm_num

private theorem prime_oneHundredTwoCV_10427 : Nat.Prime 10427 := by norm_num

private theorem prime_oneHundredTwoCV_10499 : Nat.Prime 10499 := by norm_num

private theorem prime_oneHundredTwoCV_10831 : Nat.Prime 10831 := by norm_num

private theorem prime_oneHundredTwoCV_10909 : Nat.Prime 10909 := by norm_num

private theorem prime_oneHundredTwoCV_11279 : Nat.Prime 11279 := by norm_num

private theorem prime_oneHundredTwoCV_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_oneHundredTwoCV_11677 : Nat.Prime 11677 := by norm_num

private theorem prime_oneHundredTwoCV_11903 : Nat.Prime 11903 := by norm_num

private theorem prime_oneHundredTwoCV_11941 : Nat.Prime 11941 := by norm_num

private theorem prime_oneHundredTwoCV_12553 : Nat.Prime 12553 := by norm_num

private theorem prime_oneHundredTwoCV_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_oneHundredTwoCV_13381 : Nat.Prime 13381 := by norm_num

private theorem prime_oneHundredTwoCV_13397 : Nat.Prime 13397 := by norm_num

private theorem prime_oneHundredTwoCV_13829 : Nat.Prime 13829 := by norm_num

private theorem prime_oneHundredTwoCV_13903 : Nat.Prime 13903 := by norm_num

private theorem prime_oneHundredTwoCV_13933 : Nat.Prime 13933 := by norm_num

private theorem prime_oneHundredTwoCV_13967 : Nat.Prime 13967 := by norm_num

private theorem prime_oneHundredTwoCV_14243 : Nat.Prime 14243 := by norm_num

private theorem prime_oneHundredTwoCV_15277 : Nat.Prime 15277 := by norm_num

private theorem prime_oneHundredTwoCV_15919 : Nat.Prime 15919 := by norm_num

private theorem prime_oneHundredTwoCV_16103 : Nat.Prime 16103 := by norm_num

private theorem prime_oneHundredTwoCV_18223 : Nat.Prime 18223 := by norm_num

private theorem prime_oneHundredTwoCV_18229 : Nat.Prime 18229 := by norm_num

private theorem prime_oneHundredTwoCV_18539 : Nat.Prime 18539 := by norm_num

private theorem prime_oneHundredTwoCV_19379 : Nat.Prime 19379 := by norm_num

private theorem prime_oneHundredTwoCV_19489 : Nat.Prime 19489 := by norm_num

private theorem prime_oneHundredTwoCV_20021 : Nat.Prime 20021 := by norm_num

private theorem prime_oneHundredTwoCV_20063 : Nat.Prime 20063 := by norm_num

private theorem prime_oneHundredTwoCV_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwoCV_20963 : Nat.Prime 20963 := by norm_num

private theorem prime_oneHundredTwoCV_21107 : Nat.Prime 21107 := by norm_num

private theorem prime_oneHundredTwoCV_21191 : Nat.Prime 21191 := by norm_num

private theorem prime_oneHundredTwoCV_25679 : Nat.Prime 25679 := by norm_num

private theorem prime_oneHundredTwoCV_26003 : Nat.Prime 26003 := by norm_num

private theorem prime_oneHundredTwoCV_26183 : Nat.Prime 26183 := by norm_num

private theorem prime_oneHundredTwoCV_26731 : Nat.Prime 26731 := by norm_num

private theorem prime_oneHundredTwoCV_27337 : Nat.Prime 27337 := by norm_num

private theorem prime_oneHundredTwoCV_27361 : Nat.Prime 27361 := by norm_num

private theorem prime_oneHundredTwoCV_27673 : Nat.Prime 27673 := by norm_num

private theorem prime_oneHundredTwoCV_27893 : Nat.Prime 27893 := by norm_num

private theorem prime_oneHundredTwoCV_28393 : Nat.Prime 28393 := by norm_num

private theorem prime_oneHundredTwoCV_28619 : Nat.Prime 28619 := by norm_num

private theorem prime_oneHundredTwoCV_28643 : Nat.Prime 28643 := by norm_num

private theorem prime_oneHundredTwoCV_30427 : Nat.Prime 30427 := by norm_num

private theorem prime_oneHundredTwoCV_30703 : Nat.Prime 30703 := by norm_num

private theorem prime_oneHundredTwoCV_31643 : Nat.Prime 31643 := by norm_num

private theorem prime_oneHundredTwoCV_32117 : Nat.Prime 32117 := by norm_num

private theorem prime_oneHundredTwoCV_34403 : Nat.Prime 34403 := by norm_num

private theorem prime_oneHundredTwoCV_35153 : Nat.Prime 35153 := by norm_num

private theorem prime_oneHundredTwoCV_36293 : Nat.Prime 36293 := by norm_num

private theorem prime_oneHundredTwoCV_36739 : Nat.Prime 36739 := by norm_num

private theorem prime_oneHundredTwoCV_37511 : Nat.Prime 37511 := by norm_num

private theorem prime_oneHundredTwoCV_38119 : Nat.Prime 38119 := by norm_num

private theorem prime_oneHundredTwoCV_38287 : Nat.Prime 38287 := by norm_num

private theorem prime_oneHundredTwoCV_39659 : Nat.Prime 39659 := by norm_num

private theorem prime_oneHundredTwoCV_43271 : Nat.Prime 43271 := by norm_num

private theorem prime_oneHundredTwoCV_45833 : Nat.Prime 45833 := by norm_num

private theorem prime_oneHundredTwoCV_47497 : Nat.Prime 47497 := by norm_num

private theorem prime_oneHundredTwoCV_50909 : Nat.Prime 50909 := by norm_num

private theorem prime_oneHundredTwoCV_53069 : Nat.Prime 53069 := by norm_num

private theorem prime_oneHundredTwoCV_54949 : Nat.Prime 54949 := by norm_num

private theorem prime_oneHundredTwoCV_55871 : Nat.Prime 55871 := by norm_num

private theorem prime_oneHundredTwoCV_58099 : Nat.Prime 58099 := by norm_num

private theorem prime_oneHundredTwoCV_63599 : Nat.Prime 63599 := by norm_num

private theorem prime_oneHundredTwoCV_67247 : Nat.Prime 67247 := by norm_num

private theorem prime_oneHundredTwoCV_68669 : Nat.Prime 68669 := by norm_num

private theorem prime_oneHundredTwoCV_69959 : Nat.Prime 69959 := by norm_num

private theorem prime_oneHundredTwoCV_73517 : Nat.Prime 73517 := by norm_num

private theorem prime_oneHundredTwoCV_80077 : Nat.Prime 80077 := by norm_num

private theorem prime_oneHundredTwoCV_82387 : Nat.Prime 82387 := by norm_num

private theorem prime_oneHundredTwoCV_91163 : Nat.Prime 91163 := by norm_num

private theorem prime_oneHundredTwoCV_94201 : Nat.Prime 94201 := by norm_num

private theorem prime_oneHundredTwoCV_105229 : Nat.Prime 105229 := by norm_num

private theorem prime_oneHundredTwoCV_105619 : Nat.Prime 105619 := by norm_num

private theorem prime_oneHundredTwoCV_106703 : Nat.Prime 106703 := by norm_num

private theorem prime_oneHundredTwoCV_108193 : Nat.Prime 108193 := by norm_num

private theorem prime_oneHundredTwoCV_109379 : Nat.Prime 109379 := by norm_num

private theorem prime_oneHundredTwoCV_109597 : Nat.Prime 109597 := by norm_num

private theorem prime_oneHundredTwoCV_110069 : Nat.Prime 110069 := by norm_num

private theorem prime_oneHundredTwoCV_112103 : Nat.Prime 112103 := by norm_num

private theorem prime_oneHundredTwoCV_112289 : Nat.Prime 112289 := by norm_num

private theorem prime_oneHundredTwoCV_116423 : Nat.Prime 116423 := by norm_num

private theorem prime_oneHundredTwoCV_123377 : Nat.Prime 123377 := by norm_num

private theorem prime_oneHundredTwoCV_125371 : Nat.Prime 125371 := by norm_num

private theorem prime_oneHundredTwoCV_128813 : Nat.Prime 128813 := by norm_num

private theorem prime_oneHundredTwoCV_128831 : Nat.Prime 128831 := by norm_num

private theorem prime_oneHundredTwoCV_130769 : Nat.Prime 130769 := by norm_num

private theorem prime_oneHundredTwoCV_135277 : Nat.Prime 135277 := by norm_num

private theorem prime_oneHundredTwoCV_138923 : Nat.Prime 138923 := by norm_num

private theorem prime_oneHundredTwoCV_141199 : Nat.Prime 141199 := by norm_num

private theorem prime_oneHundredTwoCV_145819 : Nat.Prime 145819 := by norm_num

private theorem prime_oneHundredTwoCV_167449 : Nat.Prime 167449 := by norm_num

private theorem prime_oneHundredTwoCV_168247 : Nat.Prime 168247 := by norm_num

private theorem prime_oneHundredTwoCV_173087 : Nat.Prime 173087 := by norm_num

private theorem prime_oneHundredTwoCV_180679 : Nat.Prime 180679 := by norm_num

private theorem prime_oneHundredTwoCV_190579 : Nat.Prime 190579 := by norm_num

private theorem prime_oneHundredTwoCV_198599 : Nat.Prime 198599 := by norm_num

private theorem prime_oneHundredTwoCV_207653 : Nat.Prime 207653 := by norm_num

private theorem prime_oneHundredTwoCV_207709 : Nat.Prime 207709 := by norm_num

private theorem prime_oneHundredTwoCV_215587 : Nat.Prime 215587 := by norm_num

private theorem prime_oneHundredTwoCV_237631 : Nat.Prime 237631 := by norm_num

private theorem prime_oneHundredTwoCV_238339 : Nat.Prime 238339 := by norm_num

private theorem prime_oneHundredTwoCV_238709 : Nat.Prime 238709 := by norm_num

private theorem prime_oneHundredTwoCV_241337 : Nat.Prime 241337 := by norm_num

private theorem prime_oneHundredTwoCV_257321 : Nat.Prime 257321 := by norm_num

private theorem prime_oneHundredTwoCV_267671 : Nat.Prime 267671 := by norm_num

private theorem prime_oneHundredTwoCV_287321 : Nat.Prime 287321 := by norm_num

private theorem prime_oneHundredTwoCV_292343 : Nat.Prime 292343 := by norm_num

private theorem prime_oneHundredTwoCV_295727 : Nat.Prime 295727 := by norm_num

private theorem prime_oneHundredTwoCV_298477 : Nat.Prime 298477 := by norm_num

private theorem prime_oneHundredTwoCV_300779 : Nat.Prime 300779 := by norm_num

private theorem prime_oneHundredTwoCV_317159 : Nat.Prime 317159 := by norm_num

private theorem prime_oneHundredTwoCV_339187 : Nat.Prime 339187 := by norm_num

private theorem prime_oneHundredTwoCV_362581 : Nat.Prime 362581 := by norm_num

private theorem prime_oneHundredTwoCV_470783 : Nat.Prime 470783 := by norm_num

private theorem prime_oneHundredTwoCV_489887 : Nat.Prime 489887 := by norm_num

private theorem prime_oneHundredTwoCV_506993 : Nat.Prime 506993 := by norm_num

private theorem prime_oneHundredTwoCV_553507 : Nat.Prime 553507 := by norm_num

private theorem prime_oneHundredTwoCV_553627 : Nat.Prime 553627 := by norm_num

private theorem prime_oneHundredTwoCV_596749 : Nat.Prime 596749 := by norm_num

private theorem prime_oneHundredTwoCV_596803 : Nat.Prime 596803 := by norm_num

private theorem prime_oneHundredTwoCV_606743 : Nat.Prime 606743 := by norm_num

private theorem prime_oneHundredTwoCV_614167 : Nat.Prime 614167 := by norm_num

private theorem prime_oneHundredTwoCV_617119 : Nat.Prime 617119 := by norm_num

private theorem prime_oneHundredTwoCV_646619 : Nat.Prime 646619 := by norm_num

private theorem prime_oneHundredTwoCV_652279 : Nat.Prime 652279 := by norm_num

private theorem prime_oneHundredTwoCV_673793 : Nat.Prime 673793 := by norm_num

private theorem prime_oneHundredTwoCV_706523 : Nat.Prime 706523 := by norm_num

private theorem prime_oneHundredTwoCV_707953 : Nat.Prime 707953 := by norm_num

private theorem prime_oneHundredTwoCV_754223 : Nat.Prime 754223 := by norm_num

private theorem prime_oneHundredTwoCV_866513 : Nat.Prime 866513 := by norm_num

private theorem prime_oneHundredTwoCV_976489 : Nat.Prime 976489 := by norm_num

private theorem prime_oneHundredTwoCV_994453 : Nat.Prime 994453 := by norm_num

private theorem prime_oneHundredTwoCV_996263 : Nat.Prime 996263 := by norm_num

private theorem prime_oneHundredTwoCV_1094473 : Nat.Prime 1094473 := by norm_num

private theorem prime_oneHundredTwoCV_1244263 : Nat.Prime 1244263 := by norm_num

private theorem prime_oneHundredTwoCV_1250497 : Nat.Prime 1250497 := by norm_num

private theorem prime_oneHundredTwoCV_1255021 : Nat.Prime 1255021 := by norm_num

private theorem prime_oneHundredTwoCV_1292429 : Nat.Prime 1292429 := by norm_num

private theorem prime_oneHundredTwoCV_1310527 : Nat.Prime 1310527 := by norm_num

private theorem prime_oneHundredTwoCV_1475147 : Nat.Prime 1475147 := by norm_num

private theorem prime_oneHundredTwoCV_1536991 : Nat.Prime 1536991 := by norm_num

private theorem prime_oneHundredTwoCV_1600349 : Nat.Prime 1600349 := by norm_num

private theorem prime_oneHundredTwoCV_1711613 : Nat.Prime 1711613 := by norm_num

private theorem prime_oneHundredTwoCV_1750657 : Nat.Prime 1750657 := by norm_num

private theorem prime_oneHundredTwoCV_1785851 : Nat.Prime 1785851 := by norm_num

private theorem prime_oneHundredTwoCV_1802597 : Nat.Prime 1802597 := by norm_num

private theorem prime_oneHundredTwoCV_1922447 : Nat.Prime 1922447 := by norm_num

private theorem prime_oneHundredTwoCV_2044111 : Nat.Prime 2044111 := by norm_num

private theorem prime_oneHundredTwoCV_2102783 : Nat.Prime 2102783 := by norm_num

private theorem prime_oneHundredTwoCV_2134963 : Nat.Prime 2134963 := by norm_num

private theorem prime_oneHundredTwoCV_2352289 : Nat.Prime 2352289 := by norm_num

private theorem prime_oneHundredTwoCV_2417603 : Nat.Prime 2417603 := by norm_num

private theorem prime_oneHundredTwoCV_2514767 : Nat.Prime 2514767 := by norm_num

private theorem prime_oneHundredTwoCV_2598751 : Nat.Prime 2598751 := by norm_num

private theorem prime_oneHundredTwoCV_2740733 : Nat.Prime 2740733 := by norm_num

private theorem prime_oneHundredTwoCV_2747449 : Nat.Prime 2747449 := by norm_num

private theorem prime_oneHundredTwoCV_2842253 : Nat.Prime 2842253 := by norm_num

private theorem prime_oneHundredTwoCV_2857381 : Nat.Prime 2857381 := by norm_num

private theorem prime_oneHundredTwoCV_2935157 : Nat.Prime 2935157 := by norm_num

private theorem prime_oneHundredTwoCV_3055501 : Nat.Prime 3055501 := by norm_num

private theorem prime_oneHundredTwoCV_3174167 : Nat.Prime 3174167 := by norm_num

private theorem prime_oneHundredTwoCV_3375173 : Nat.Prime 3375173 := by norm_num

private theorem prime_oneHundredTwoCV_3469049 : Nat.Prime 3469049 := by norm_num

private theorem prime_oneHundredTwoCV_3504481 : Nat.Prime 3504481 := by norm_num

private theorem prime_oneHundredTwoCV_3927943 : Nat.Prime 3927943 := by norm_num

private theorem prime_oneHundredTwoCV_4236983 : Nat.Prime 4236983 := by norm_num

private theorem prime_oneHundredTwoCV_4243453 : Nat.Prime 4243453 := by norm_num

private theorem prime_oneHundredTwoCV_4697453 : Nat.Prime 4697453 := by norm_num

private theorem prime_oneHundredTwoCV_4866599 : Nat.Prime 4866599 := by norm_num

private theorem prime_oneHundredTwoCV_4880279 : Nat.Prime 4880279 := by norm_num

private theorem prime_oneHundredTwoCV_5426387 : Nat.Prime 5426387 := by norm_num

private theorem prime_oneHundredTwoCV_5685499 : Nat.Prime 5685499 := by norm_num

private theorem prime_oneHundredTwoCV_5992421 : Nat.Prime 5992421 := by norm_num

private theorem prime_oneHundredTwoCV_6100111 : Nat.Prime 6100111 := by norm_num

private theorem prime_oneHundredTwoCV_6271787 : Nat.Prime 6271787 := by norm_num

private theorem prime_oneHundredTwoCV_7032829 : Nat.Prime 7032829 := by norm_num

private theorem prime_oneHundredTwoCV_8081299 : Nat.Prime 8081299 := by norm_num

private theorem prime_oneHundredTwoCV_8329157 : Nat.Prime 8329157 := by norm_num

private theorem prime_oneHundredTwoCV_8820923 : Nat.Prime 8820923 := by norm_num

private theorem prime_oneHundredTwoCV_8918069 : Nat.Prime 8918069 := by norm_num

private theorem prime_oneHundredTwoCV_8980079 : Nat.Prime 8980079 := by norm_num

private theorem prime_oneHundredTwoCV_9353189 : Nat.Prime 9353189 := by norm_num

private theorem prime_oneHundredTwoCV_10081711 : Nat.Prime 10081711 := by norm_num

private theorem prime_oneHundredTwoCV_10131601 : Nat.Prime 10131601 := by norm_num

private theorem prime_oneHundredTwoCV_10651651 : Nat.Prime 10651651 := by norm_num

private theorem prime_oneHundredTwoCV_10738801 : Nat.Prime 10738801 := by norm_num

private theorem prime_oneHundredTwoCV_10826177 : Nat.Prime 10826177 := by norm_num

private theorem prime_oneHundredTwoCV_10828241 : Nat.Prime 10828241 := by norm_num

private theorem prime_oneHundredTwoCV_11600627 : Nat.Prime 11600627 := by norm_num

private theorem prime_oneHundredTwoCV_11730233 : Nat.Prime 11730233 := by norm_num

private theorem prime_oneHundredTwoCV_13157437 : Nat.Prime 13157437 := by norm_num

private theorem prime_oneHundredTwoCV_13597063 : Nat.Prime 13597063 := by norm_num

private theorem prime_oneHundredTwoCV_14419289 : Nat.Prime 14419289 := by norm_num

private theorem prime_oneHundredTwoCV_16776289 : Nat.Prime 16776289 := by norm_num

private theorem prime_oneHundredTwoCV_17920367 : Nat.Prime 17920367 := by norm_num

private theorem prime_oneHundredTwoCV_18773917 : Nat.Prime 18773917 := by norm_num

private theorem prime_oneHundredTwoCV_19423489 : Nat.Prime 19423489 := by norm_num

private theorem prime_oneHundredTwoCV_19626001 : Nat.Prime 19626001 := by norm_num

private theorem prime_oneHundredTwoCV_19684871 : Nat.Prime 19684871 := by norm_num

private theorem prime_oneHundredTwoCV_22641343 : Nat.Prime 22641343 := by norm_num

private theorem prime_oneHundredTwoCV_23223209 : Nat.Prime 23223209 := by norm_num

private theorem prime_oneHundredTwoCV_23510849 : Nat.Prime 23510849 := by norm_num

private theorem prime_oneHundredTwoCV_24063043 : Nat.Prime 24063043 := by norm_num

private theorem prime_oneHundredTwoCV_24361483 : Nat.Prime 24361483 := by norm_num

private theorem prime_oneHundredTwoCV_24537593 : Nat.Prime 24537593 := by norm_num

private theorem prime_oneHundredTwoCV_24922517 : Nat.Prime 24922517 := by norm_num

private theorem prime_oneHundredTwoCV_25049119 : Nat.Prime 25049119 := by norm_num

private theorem prime_oneHundredTwoCV_28439897 : Nat.Prime 28439897 := by norm_num

private theorem prime_oneHundredTwoCV_29158291 : Nat.Prime 29158291 := by norm_num

private theorem prime_oneHundredTwoCV_29885783 : Nat.Prime 29885783 := by norm_num

private theorem prime_oneHundredTwoCV_32206667 : Nat.Prime 32206667 := by
  apply lucas_primality 32206667 (2 : ZMod 32206667)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (157, 1), (941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (157, 1), (941, 1)] : List FactorBlock).map factorBlockValue).prod) = 32206667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_109
      · exact prime_oneHundredTwoCV_157
      · exact prime_oneHundredTwoCV_941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32206667) ^ 16103333 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32206667) ^ 295474 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32206667) ^ 205138 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32206667) ^ 34226 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_32702827 : Nat.Prime 32702827 := by
  apply lucas_primality 32702827 (11 : ZMod 32702827)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (18229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (18229, 1)] : List FactorBlock).map factorBlockValue).prod) = 32702827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_18229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 32702827) ^ 16351413 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 32702827) ^ 10900942 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 32702827) ^ 2515602 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 32702827) ^ 1421862 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 32702827) ^ 1794 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_32850247 : Nat.Prime 32850247 := by
  apply lucas_primality 32850247 (6 : ZMod 32850247)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod) = 32850247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_38287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 32850247) ^ 16425123 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 32850247) ^ 10950082 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 32850247) ^ 2986386 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 32850247) ^ 2526942 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 32850247) ^ 858 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_33341993 : Nat.Prime 33341993 := by
  apply lucas_primality 33341993 (3 : ZMod 33341993)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1181, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1181, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) = 33341993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_1181
      · exact prime_oneHundredTwoCV_3529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33341993) ^ 16670996 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33341993) ^ 28232 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33341993) ^ 9448 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_33380351 : Nat.Prime 33380351 := by
  apply lucas_primality 33380351 (14 : ZMod 33380351)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (173, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (173, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 33380351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_173
      · exact prime_oneHundredTwoCV_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 33380351) ^ 16690175 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 33380351) ^ 6676070 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 33380351) ^ 1963550 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 33380351) ^ 192950 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 33380351) ^ 147050 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_34867981 : Nat.Prime 34867981 := by
  apply lucas_primality 34867981 (2 : ZMod 34867981)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (27673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (27673, 1)] : List FactorBlock).map factorBlockValue).prod) = 34867981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_27673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34867981) ^ 17433990 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867981) ^ 11622660 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867981) ^ 6973596 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867981) ^ 4981140 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867981) ^ 1260 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_35018183 : Nat.Prime 35018183 := by
  apply lucas_primality 35018183 (5 : ZMod 35018183)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (509, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (509, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 35018183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_41
      · exact prime_oneHundredTwoCV_509
      · exact prime_oneHundredTwoCV_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35018183) ^ 17509091 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 35018183) ^ 854102 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 35018183) ^ 68798 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 35018183) ^ 41738 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_35861753 : Nat.Prime 35861753 := by
  apply lucas_primality 35861753 (3 : ZMod 35861753)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (127, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (127, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35861753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_47
      · exact prime_oneHundredTwoCV_127
      · exact prime_oneHundredTwoCV_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35861753) ^ 17930876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35861753) ^ 763016 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35861753) ^ 282376 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35861753) ^ 47752 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_37341151 : Nat.Prime 37341151 := by
  apply lucas_primality 37341151 (6 : ZMod 37341151)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 37341151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_53
      · exact prime_oneHundredTwoCV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37341151) ^ 18670575 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 37341151) ^ 12447050 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 37341151) ^ 7468230 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 37341151) ^ 5334450 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 37341151) ^ 3394650 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 37341151) ^ 704550 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 37341151) ^ 612150 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_38353823 : Nat.Prime 38353823 := by
  apply lucas_primality 38353823 (5 : ZMod 38353823)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1475147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1475147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38353823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_1475147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 38353823) ^ 19176911 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 38353823) ^ 2950294 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 38353823) ^ 26 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_38734273 : Nat.Prime 38734273 := by
  apply lucas_primality 38734273 (5 : ZMod 38734273)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (67247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (67247, 1)] : List FactorBlock).map factorBlockValue).prod) = 38734273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_67247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 38734273) ^ 19367136 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 38734273) ^ 12911424 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 38734273) ^ 576 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_39713719 : Nat.Prime 39713719 := by
  apply lucas_primality 39713719 (11 : ZMod 39713719)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (683, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (683, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) = 39713719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_683
      · exact prime_oneHundredTwoCV_881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39713719) ^ 19856859 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 39713719) ^ 13237906 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 39713719) ^ 3610338 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 39713719) ^ 58146 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 39713719) ^ 45078 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_43181219 : Nat.Prime 43181219 := by
  apply lucas_primality 43181219 (2 : ZMod 43181219)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (109597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (109597, 1)] : List FactorBlock).map factorBlockValue).prod) = 43181219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_197
      · exact prime_oneHundredTwoCV_109597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43181219) ^ 21590609 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43181219) ^ 219194 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43181219) ^ 394 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_45783767 : Nat.Prime 45783767 := by
  apply lucas_primality 45783767 (5 : ZMod 45783767)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (163, 1), (20063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (163, 1), (20063, 1)] : List FactorBlock).map factorBlockValue).prod) = 45783767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_163
      · exact prime_oneHundredTwoCV_20063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45783767) ^ 22891883 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 45783767) ^ 6540538 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 45783767) ^ 280882 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 45783767) ^ 2282 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_46298561 : Nat.Prime 46298561 := by
  apply lucas_primality 46298561 (6 : ZMod 46298561)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (11, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (11, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) = 46298561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_1879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 46298561) ^ 23149280 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 46298561) ^ 9259712 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 46298561) ^ 6614080 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 46298561) ^ 4208960 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 46298561) ^ 24640 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_50174297 : Nat.Prime 50174297 := by
  apply lucas_primality 50174297 (3 : ZMod 50174297)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6271787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6271787, 1)] : List FactorBlock).map factorBlockValue).prod) = 50174297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_6271787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 50174297) ^ 25087148 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50174297) ^ 8 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_52519711 : Nat.Prime 52519711 := by
  apply lucas_primality 52519711 (15 : ZMod 52519711)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1750657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1750657, 1)] : List FactorBlock).map factorBlockValue).prod) = 52519711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_1750657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 52519711) ^ 26259855 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 52519711) ^ 17506570 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 52519711) ^ 10503942 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 52519711) ^ 30 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_57911291 : Nat.Prime 57911291 := by
  apply lucas_primality 57911291 (2 : ZMod 57911291)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (281, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (281, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 57911291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_281
      · exact prime_oneHundredTwoCV_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57911291) ^ 28955645 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57911291) ^ 11582258 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57911291) ^ 1565170 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57911291) ^ 206090 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57911291) ^ 103970 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_63909907 : Nat.Prime 63909907 := by
  apply lucas_primality 63909907 (2 : ZMod 63909907)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10651651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10651651, 1)] : List FactorBlock).map factorBlockValue).prod) = 63909907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_10651651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63909907) ^ 31954953 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 63909907) ^ 21303302 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 63909907) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_67937063 : Nat.Prime 67937063 := by
  apply lucas_primality 67937063 (5 : ZMod 67937063)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (506993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (506993, 1)] : List FactorBlock).map factorBlockValue).prod) = 67937063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_67
      · exact prime_oneHundredTwoCV_506993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67937063) ^ 33968531 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 67937063) ^ 1013986 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 67937063) ^ 134 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_69040021 : Nat.Prime 69040021 := by
  apply lucas_primality 69040021 (2 : ZMod 69040021)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (23, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (23, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) = 69040021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_1021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69040021) ^ 34520010 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69040021) ^ 23013340 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69040021) ^ 13808004 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69040021) ^ 9862860 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69040021) ^ 3001740 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69040021) ^ 67620 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_70940633 : Nat.Prime 70940633 := by
  apply lucas_primality 70940633 (3 : ZMod 70940633)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 3), (103, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 3), (103, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 70940633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_103
      · exact prime_oneHundredTwoCV_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70940633) ^ 35470316 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70940633) ^ 10134376 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70940633) ^ 688744 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70940633) ^ 282632 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_71723507 : Nat.Prime 71723507 := by
  apply lucas_primality 71723507 (2 : ZMod 71723507)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (35861753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (35861753, 1)] : List FactorBlock).map factorBlockValue).prod) = 71723507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_35861753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 71723507) ^ 35861753 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 71723507) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_75197179 : Nat.Prime 75197179 := by
  apply lucas_primality 75197179 (2 : ZMod 75197179)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (596803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (596803, 1)] : List FactorBlock).map factorBlockValue).prod) = 75197179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_596803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75197179) ^ 37598589 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75197179) ^ 25065726 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75197179) ^ 10742454 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75197179) ^ 126 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_90565373 : Nat.Prime 90565373 := by
  apply lucas_primality 90565373 (2 : ZMod 90565373)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (22641343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (22641343, 1)] : List FactorBlock).map factorBlockValue).prod) = 90565373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_22641343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 90565373) ^ 45282686 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 90565373) ^ 4 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_91935733 : Nat.Prime 91935733 := by
  apply lucas_primality 91935733 (2 : ZMod 91935733)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1094473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1094473, 1)] : List FactorBlock).map factorBlockValue).prod) = 91935733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_1094473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91935733) ^ 45967866 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 91935733) ^ 30645244 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 91935733) ^ 13133676 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 91935733) ^ 84 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_96372361 : Nat.Prime 96372361 := by
  apply lucas_primality 96372361 (13 : ZMod 96372361)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (167, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (167, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 96372361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_167
      · exact prime_oneHundredTwoCV_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 96372361) ^ 48186180 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 96372361) ^ 32124120 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 96372361) ^ 19274472 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 96372361) ^ 13767480 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 96372361) ^ 577080 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 96372361) ^ 420840 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_100196477 : Nat.Prime 100196477 := by
  apply lucas_primality 100196477 (2 : ZMod 100196477)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25049119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25049119, 1)] : List FactorBlock).map factorBlockValue).prod) = 100196477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_25049119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 100196477) ^ 50098238 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 100196477) ^ 4 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_100409923 : Nat.Prime 100409923 := by
  apply lucas_primality 100409923 (2 : ZMod 100409923)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (109379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (109379, 1)] : List FactorBlock).map factorBlockValue).prod) = 100409923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_109379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100409923) ^ 50204961 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 100409923) ^ 33469974 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 100409923) ^ 5906466 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 100409923) ^ 918 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_102143891 : Nat.Prime 102143891 := by
  apply lucas_primality 102143891 (2 : ZMod 102143891)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (167449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (167449, 1)] : List FactorBlock).map factorBlockValue).prod) = 102143891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_61
      · exact prime_oneHundredTwoCV_167449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102143891) ^ 51071945 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143891) ^ 20428778 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143891) ^ 1674490 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143891) ^ 610 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_106271903 : Nat.Prime 106271903 := by
  apply lucas_primality 106271903 (5 : ZMod 106271903)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 2), (13381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 2), (13381, 1)] : List FactorBlock).map factorBlockValue).prod) = 106271903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_13381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 106271903) ^ 53135951 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 106271903) ^ 9661082 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 106271903) ^ 5593258 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 106271903) ^ 7942 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_115800499 : Nat.Prime 115800499 := by
  apply lucas_primality 115800499 (3 : ZMod 115800499)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 1), (34403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 1), (34403, 1)] : List FactorBlock).map factorBlockValue).prod) = 115800499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_34403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115800499) ^ 57900249 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 115800499) ^ 38600166 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 115800499) ^ 10527318 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 115800499) ^ 6811794 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 115800499) ^ 3366 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_115822583 : Nat.Prime 115822583 := by
  apply lucas_primality 115822583 (5 : ZMod 115822583)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57911291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57911291, 1)] : List FactorBlock).map factorBlockValue).prod) = 115822583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_57911291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 115822583) ^ 57911291 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 115822583) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_117756007 : Nat.Prime 117756007 := by
  apply lucas_primality 117756007 (3 : ZMod 117756007)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19626001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19626001, 1)] : List FactorBlock).map factorBlockValue).prod) = 117756007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_19626001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 117756007) ^ 58878003 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 117756007) ^ 39252002 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 117756007) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_122133779 : Nat.Prime 122133779 := by
  apply lucas_primality 122133779 (2 : ZMod 122133779)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4697453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4697453, 1)] : List FactorBlock).map factorBlockValue).prod) = 122133779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_4697453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 122133779) ^ 61066889 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 122133779) ^ 9394906 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 122133779) ^ 26 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_126880591 : Nat.Prime 126880591 := by
  apply lucas_primality 126880591 (3 : ZMod 126880591)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (139, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (139, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod) = 126880591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_139
      · exact prime_oneHundredTwoCV_30427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126880591) ^ 63440295 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 126880591) ^ 42293530 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 126880591) ^ 25376118 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 126880591) ^ 912810 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 126880591) ^ 4170 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_127109491 : Nat.Prime 127109491 := by
  apply lucas_primality 127109491 (2 : ZMod 127109491)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4236983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4236983, 1)] : List FactorBlock).map factorBlockValue).prod) = 127109491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_4236983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 127109491) ^ 63554745 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127109491) ^ 42369830 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127109491) ^ 25421898 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127109491) ^ 30 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_127556983 : Nat.Prime 127556983 := by
  apply lucas_primality 127556983 (3 : ZMod 127556983)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (37, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (37, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) = 127556983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_27361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127556983) ^ 63778491 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 127556983) ^ 42518994 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 127556983) ^ 18222426 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 127556983) ^ 3447486 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 127556983) ^ 4662 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_146078369 : Nat.Prime 146078369 := by
  apply lucas_primality 146078369 (3 : ZMod 146078369)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (123377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (123377, 1)] : List FactorBlock).map factorBlockValue).prod) = 146078369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_123377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146078369) ^ 73039184 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 146078369) ^ 3948064 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 146078369) ^ 1184 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_152793629 : Nat.Prime 152793629 := by
  apply lucas_primality 152793629 (2 : ZMod 152793629)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (113, 1), (26003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (113, 1), (26003, 1)] : List FactorBlock).map factorBlockValue).prod) = 152793629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_113
      · exact prime_oneHundredTwoCV_26003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152793629) ^ 76396814 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 152793629) ^ 11753356 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 152793629) ^ 1352156 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 152793629) ^ 5876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_175405801 : Nat.Prime 175405801 := by
  apply lucas_primality 175405801 (11 : ZMod 175405801)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (292343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (292343, 1)] : List FactorBlock).map factorBlockValue).prod) = 175405801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_292343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 175405801) ^ 87702900 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 175405801) ^ 58468600 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 175405801) ^ 35081160 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 175405801) ^ 600 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_190812689 : Nat.Prime 190812689 := by
  apply lucas_primality 190812689 (3 : ZMod 190812689)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (31, 1), (41, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (31, 1), (41, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 190812689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_41
      · exact prime_oneHundredTwoCV_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 190812689) ^ 95406344 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190812689) ^ 17346608 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190812689) ^ 6155248 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190812689) ^ 4653968 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190812689) ^ 223696 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_270853787 : Nat.Prime 270853787 := by
  apply lucas_primality 270853787 (2 : ZMod 270853787)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (317159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (317159, 1)] : List FactorBlock).map factorBlockValue).prod) = 270853787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_61
      · exact prime_oneHundredTwoCV_317159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 270853787) ^ 135426893 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 270853787) ^ 38693398 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 270853787) ^ 4440226 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 270853787) ^ 854 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_289215937 : Nat.Prime 289215937 := by
  apply lucas_primality 289215937 (5 : ZMod 289215937)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (43, 1), (11677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (43, 1), (11677, 1)] : List FactorBlock).map factorBlockValue).prod) = 289215937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_43
      · exact prime_oneHundredTwoCV_11677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 289215937) ^ 144607968 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 289215937) ^ 96405312 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 289215937) ^ 6725952 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 289215937) ^ 24768 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_305587259 : Nat.Prime 305587259 := by
  apply lucas_primality 305587259 (2 : ZMod 305587259)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (152793629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (152793629, 1)] : List FactorBlock).map factorBlockValue).prod) = 305587259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_152793629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 305587259) ^ 152793629 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 305587259) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_329151887 : Nat.Prime 329151887 := by
  apply lucas_primality 329151887 (5 : ZMod 329151887)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23510849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23510849, 1)] : List FactorBlock).map factorBlockValue).prod) = 329151887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_23510849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 329151887) ^ 164575943 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 329151887) ^ 47021698 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 329151887) ^ 14 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_329234929 : Nat.Prime 329234929 := by
  apply lucas_primality 329234929 (29 : ZMod 329234929)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (239, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (239, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) = 329234929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_239
      · exact prime_oneHundredTwoCV_2609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 329234929) ^ 164617464 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (29 : ZMod 329234929) ^ 109744976 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (29 : ZMod 329234929) ^ 29930448 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (29 : ZMod 329234929) ^ 1377552 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (29 : ZMod 329234929) ^ 126192 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_332458733 : Nat.Prime 332458733 := by
  apply lucas_primality 332458733 (2 : ZMod 332458733)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (19, 1), (257321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (19, 1), (257321, 1)] : List FactorBlock).map factorBlockValue).prod) = 332458733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_257321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 332458733) ^ 166229366 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 332458733) ^ 19556396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 332458733) ^ 17497828 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 332458733) ^ 1292 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_339893497 : Nat.Prime 339893497 := by
  apply lucas_primality 339893497 (7 : ZMod 339893497)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (431, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (431, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 339893497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_431
      · exact prime_oneHundredTwoCV_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 339893497) ^ 169946748 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 339893497) ^ 113297832 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 339893497) ^ 788616 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 339893497) ^ 279288 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_345137173 : Nat.Prime 345137173 := by
  apply lucas_primality 345137173 (5 : ZMod 345137173)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1250497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1250497, 1)] : List FactorBlock).map factorBlockValue).prod) = 345137173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_1250497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 345137173) ^ 172568586 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 345137173) ^ 115045724 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 345137173) ^ 15005964 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 345137173) ^ 276 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_380661763 : Nat.Prime 380661763 := by
  apply lucas_primality 380661763 (5 : ZMod 380661763)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4880279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4880279, 1)] : List FactorBlock).map factorBlockValue).prod) = 380661763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_4880279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 380661763) ^ 190330881 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 380661763) ^ 126887254 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 380661763) ^ 29281674 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 380661763) ^ 78 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_400773641 : Nat.Prime 400773641 := by
  apply lucas_primality 400773641 (13 : ZMod 400773641)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 2), (37, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 2), (37, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 400773641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 400773641) ^ 200386820 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 400773641) ^ 80154728 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 400773641) ^ 23574920 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 400773641) ^ 10831720 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 400773641) ^ 427720 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_466129493 : Nat.Prime 466129493 := by
  apply lucas_primality 466129493 (2 : ZMod 466129493)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (2842253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (2842253, 1)] : List FactorBlock).map factorBlockValue).prod) = 466129493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_41
      · exact prime_oneHundredTwoCV_2842253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 466129493) ^ 233064746 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 466129493) ^ 11369012 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 466129493) ^ 164 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_466787903 : Nat.Prime 466787903 := by
  apply lucas_primality 466787903 (7 : ZMod 466787903)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (33341993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (33341993, 1)] : List FactorBlock).map factorBlockValue).prod) = 466787903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_33341993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 466787903) ^ 233393951 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 466787903) ^ 66683986 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 466787903) ^ 14 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_491065429 : Nat.Prime 491065429 := by
  apply lucas_primality 491065429 (2 : ZMod 491065429)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (607, 1), (9631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (607, 1), (9631, 1)] : List FactorBlock).map factorBlockValue).prod) = 491065429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_607
      · exact prime_oneHundredTwoCV_9631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 491065429) ^ 245532714 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 491065429) ^ 163688476 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 491065429) ^ 70152204 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 491065429) ^ 809004 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 491065429) ^ 50988 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_508931711 : Nat.Prime 508931711 := by
  apply lucas_primality 508931711 (7 : ZMod 508931711)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (137, 1), (53069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (137, 1), (53069, 1)] : List FactorBlock).map factorBlockValue).prod) = 508931711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_137
      · exact prime_oneHundredTwoCV_53069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 508931711) ^ 254465855 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 508931711) ^ 101786342 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 508931711) ^ 72704530 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 508931711) ^ 3714830 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 508931711) ^ 9590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_510227933 : Nat.Prime 510227933 := by
  apply lucas_primality 510227933 (2 : ZMod 510227933)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127556983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127556983, 1)] : List FactorBlock).map factorBlockValue).prod) = 510227933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_127556983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 510227933) ^ 255113966 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 510227933) ^ 4 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_563975593 : Nat.Prime 563975593 := by
  apply lucas_primality 563975593 (7 : ZMod 563975593)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 1), (215587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 1), (215587, 1)] : List FactorBlock).map factorBlockValue).prod) = 563975593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_109
      · exact prime_oneHundredTwoCV_215587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 563975593) ^ 281987796 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 563975593) ^ 187991864 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 563975593) ^ 5174088 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 563975593) ^ 2616 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_612863347 : Nat.Prime 612863347 := by
  apply lucas_primality 612863347 (2 : ZMod 612863347)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (102143891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (102143891, 1)] : List FactorBlock).map factorBlockValue).prod) = 612863347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_102143891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 612863347) ^ 306431673 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 612863347) ^ 204287782 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 612863347) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_649927081 : Nat.Prime 649927081 := by
  apply lucas_primality 649927081 (14 : ZMod 649927081)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (41, 1), (4003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (41, 1), (4003, 1)] : List FactorBlock).map factorBlockValue).prod) = 649927081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_41
      · exact prime_oneHundredTwoCV_4003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 649927081) ^ 324963540 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 649927081) ^ 216642360 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 649927081) ^ 129985416 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 649927081) ^ 59084280 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 649927081) ^ 15851880 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 649927081) ^ 162360 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_676128071 : Nat.Prime 676128071 := by
  apply lucas_primality 676128071 (11 : ZMod 676128071)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2633, 1), (25679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2633, 1), (25679, 1)] : List FactorBlock).map factorBlockValue).prod) = 676128071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_2633
      · exact prime_oneHundredTwoCV_25679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 676128071) ^ 338064035 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 676128071) ^ 135225614 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 676128071) ^ 256790 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 676128071) ^ 26330 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_706820557 : Nat.Prime 706820557 := by
  apply lucas_primality 706820557 (2 : ZMod 706820557)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (89, 1), (50909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (89, 1), (50909, 1)] : List FactorBlock).map factorBlockValue).prod) = 706820557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_89
      · exact prime_oneHundredTwoCV_50909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 706820557) ^ 353410278 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 706820557) ^ 235606852 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 706820557) ^ 54370812 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 706820557) ^ 7941804 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 706820557) ^ 13884 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_716382577 : Nat.Prime 716382577 := by
  apply lucas_primality 716382577 (5 : ZMod 716382577)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (13, 1), (18223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (13, 1), (18223, 1)] : List FactorBlock).map factorBlockValue).prod) = 716382577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_18223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 716382577) ^ 358191288 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 716382577) ^ 238794192 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 716382577) ^ 102340368 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 716382577) ^ 55106352 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 716382577) ^ 39312 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1029386543 : Nat.Prime 1029386543 := by
  apply lucas_primality 1029386543 (5 : ZMod 1029386543)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (1367, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (1367, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 1029386543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_71
      · exact prime_oneHundredTwoCV_1367
      · exact prime_oneHundredTwoCV_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1029386543) ^ 514693271 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1029386543) ^ 14498402 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1029386543) ^ 753026 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1029386543) ^ 194114 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1037121121 : Nat.Prime 1037121121 := by
  apply lucas_primality 1037121121 (19 : ZMod 1037121121)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 1), (31, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 1), (31, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037121121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_3319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1037121121) ^ 518560560 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 1037121121) ^ 345707040 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 1037121121) ^ 207424224 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 1037121121) ^ 148160160 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 1037121121) ^ 33455520 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 1037121121) ^ 312480 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1037592019 : Nat.Prime 1037592019 := by
  apply lucas_primality 1037592019 (3 : ZMod 1037592019)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (2134963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (2134963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037592019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_2134963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1037592019) ^ 518796009 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037592019) ^ 345864006 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037592019) ^ 486 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1071778067 : Nat.Prime 1071778067 := by
  apply lucas_primality 1071778067 (5 : ZMod 1071778067)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (887, 1), (19489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (887, 1), (19489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1071778067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_887
      · exact prime_oneHundredTwoCV_19489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1071778067) ^ 535889033 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071778067) ^ 34573486 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071778067) ^ 1208318 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071778067) ^ 54994 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1079333263 : Nat.Prime 1079333263 := by
  apply lucas_primality 1079333263 (6 : ZMod 1079333263)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (31, 1), (30703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (31, 1), (30703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079333263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_30703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1079333263) ^ 539666631 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079333263) ^ 359777754 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079333263) ^ 154190466 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079333263) ^ 34817202 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079333263) ^ 35154 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1125728803 : Nat.Prime 1125728803 := by
  apply lucas_primality 1125728803 (3 : ZMod 1125728803)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (5685499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (5685499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1125728803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_5685499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1125728803) ^ 562864401 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125728803) ^ 375242934 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125728803) ^ 102338982 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125728803) ^ 198 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1138849787 : Nat.Prime 1138849787 := by
  apply lucas_primality 1138849787 (2 : ZMod 1138849787)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (73, 1), (116423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (73, 1), (116423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1138849787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_67
      · exact prime_oneHundredTwoCV_73
      · exact prime_oneHundredTwoCV_116423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1138849787) ^ 569424893 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138849787) ^ 16997758 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138849787) ^ 15600682 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138849787) ^ 9782 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1151274511 : Nat.Prime 1151274511 := by
  apply lucas_primality 1151274511 (14 : ZMod 1151274511)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (113, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (113, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1151274511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_113
      · exact prime_oneHundredTwoCV_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1151274511) ^ 575637255 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1151274511) ^ 383758170 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1151274511) ^ 230254902 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1151274511) ^ 67722030 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1151274511) ^ 10188270 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1151274511) ^ 172890 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1177560071 : Nat.Prime 1177560071 := by
  apply lucas_primality 1177560071 (7 : ZMod 1177560071)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (117756007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (117756007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1177560071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_117756007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1177560071) ^ 588780035 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1177560071) ^ 235512014 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1177560071) ^ 10 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1190038771 : Nat.Prime 1190038771 := by
  apply lucas_primality 1190038771 (2 : ZMod 1190038771)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (37, 1), (139, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (37, 1), (139, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190038771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_139
      · exact prime_oneHundredTwoCV_857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1190038771) ^ 595019385 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190038771) ^ 396679590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190038771) ^ 238007754 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190038771) ^ 32163210 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190038771) ^ 8561430 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190038771) ^ 1388610 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1330153333 : Nat.Prime 1330153333 := by
  apply lucas_primality 1330153333 (2 : ZMod 1330153333)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (367, 1), (9743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (367, 1), (9743, 1)] : List FactorBlock).map factorBlockValue).prod) = 1330153333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_367
      · exact prime_oneHundredTwoCV_9743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1330153333) ^ 665076666 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1330153333) ^ 443384444 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1330153333) ^ 42908172 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1330153333) ^ 3624396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1330153333) ^ 136524 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1367983801 : Nat.Prime 1367983801 := by
  apply lucas_primality 1367983801 (17 : ZMod 1367983801)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (457, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (457, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1367983801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_457
      · exact prime_oneHundredTwoCV_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1367983801) ^ 683991900 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1367983801) ^ 455994600 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1367983801) ^ 273596760 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1367983801) ^ 2993400 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1367983801) ^ 822600 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1374105209 : Nat.Prime 1374105209 := by
  apply lucas_primality 1374105209 (3 : ZMod 1374105209)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (24537593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (24537593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1374105209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_24537593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1374105209) ^ 687052604 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1374105209) ^ 196300744 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1374105209) ^ 56 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1885120513 : Nat.Prime 1885120513 := by
  apply lucas_primality 1885120513 (5 : ZMod 1885120513)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 1), (11, 1), (27893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 1), (11, 1), (27893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1885120513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_27893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1885120513) ^ 942560256 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885120513) ^ 628373504 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885120513) ^ 171374592 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885120513) ^ 67584 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2105521013 : Nat.Prime 2105521013 := by
  apply lucas_primality 2105521013 (2 : ZMod 2105521013)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (75197179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (75197179, 1)] : List FactorBlock).map factorBlockValue).prod) = 2105521013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_75197179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2105521013) ^ 1052760506 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105521013) ^ 300788716 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105521013) ^ 28 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2322047407 : Nat.Prime 2322047407 := by
  apply lucas_primality 2322047407 (3 : ZMod 2322047407)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (443, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (443, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2322047407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_443
      · exact prime_oneHundredTwoCV_3373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2322047407) ^ 1161023703 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322047407) ^ 774015802 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322047407) ^ 331721058 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322047407) ^ 62758038 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322047407) ^ 5241642 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322047407) ^ 688422 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2796776959 : Nat.Prime 2796776959 := by
  apply lucas_primality 2796776959 (3 : ZMod 2796776959)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (466129493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (466129493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2796776959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_466129493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2796776959) ^ 1398388479 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2796776959) ^ 932258986 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2796776959) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3105048431 : Nat.Prime 3105048431 := by
  apply lucas_primality 3105048431 (11 : ZMod 3105048431)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (73, 2), (5297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (73, 2), (5297, 1)] : List FactorBlock).map factorBlockValue).prod) = 3105048431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_73
      · exact prime_oneHundredTwoCV_5297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3105048431) ^ 1552524215 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3105048431) ^ 621009686 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3105048431) ^ 282277130 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3105048431) ^ 42534910 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3105048431) ^ 586190 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3291363973 : Nat.Prime 3291363973 := by
  apply lucas_primality 3291363973 (6 : ZMod 3291363973)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (7032829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (7032829, 1)] : List FactorBlock).map factorBlockValue).prod) = 3291363973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_7032829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3291363973) ^ 1645681986 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3291363973) ^ 1097121324 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3291363973) ^ 253181844 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3291363973) ^ 468 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3741110759 : Nat.Prime 3741110759 := by
  apply lucas_primality 3741110759 (7 : ZMod 3741110759)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (67, 1), (362581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (67, 1), (362581, 1)] : List FactorBlock).map factorBlockValue).prod) = 3741110759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_67
      · exact prime_oneHundredTwoCV_362581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3741110759) ^ 1870555379 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3741110759) ^ 534444394 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3741110759) ^ 340100978 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3741110759) ^ 55837474 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3741110759) ^ 10318 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3839388869 : Nat.Prime 3839388869 := by
  apply lucas_primality 3839388869 (2 : ZMod 3839388869)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (1901, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (1901, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) = 3839388869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_1901
      · exact prime_oneHundredTwoCV_4243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3839388869) ^ 1919694434 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3839388869) ^ 548484124 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3839388869) ^ 225846404 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3839388869) ^ 2019668 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3839388869) ^ 904876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_5640693671 : Nat.Prime 5640693671 := by
  apply lucas_primality 5640693671 (14 : ZMod 5640693671)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (139, 1), (238709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (139, 1), (238709, 1)] : List FactorBlock).map factorBlockValue).prod) = 5640693671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_139
      · exact prime_oneHundredTwoCV_238709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 5640693671) ^ 2820346835 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 5640693671) ^ 1128138734 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 5640693671) ^ 331805510 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 5640693671) ^ 40580530 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 5640693671) ^ 23630 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6376314181 : Nat.Prime 6376314181 := by
  apply lucas_primality 6376314181 (6 : ZMod 6376314181)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (106271903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (106271903, 1)] : List FactorBlock).map factorBlockValue).prod) = 6376314181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_106271903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6376314181) ^ 3188157090 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376314181) ^ 2125438060 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376314181) ^ 1275262836 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376314181) ^ 60 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6473140603 : Nat.Prime 6473140603 := by
  apply lucas_primality 6473140603 (3 : ZMod 6473140603)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (29158291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (29158291, 1)] : List FactorBlock).map factorBlockValue).prod) = 6473140603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_29158291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6473140603) ^ 3236570301 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6473140603) ^ 2157713534 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6473140603) ^ 174949746 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6473140603) ^ 222 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_7011300731 : Nat.Prime 7011300731 := by
  apply lucas_primality 7011300731 (6 : ZMod 7011300731)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 3), (2044111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 3), (2044111, 1)] : List FactorBlock).map factorBlockValue).prod) = 7011300731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_2044111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 7011300731) ^ 3505650365 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7011300731) ^ 1402260146 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7011300731) ^ 1001614390 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7011300731) ^ 3430 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_7390046791 : Nat.Prime 7390046791 := by
  apply lucas_primality 7390046791 (3 : ZMod 7390046791)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11730233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11730233, 1)] : List FactorBlock).map factorBlockValue).prod) = 7390046791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11730233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7390046791) ^ 3695023395 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7390046791) ^ 2463348930 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7390046791) ^ 1478009358 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7390046791) ^ 1055720970 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7390046791) ^ 630 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_7996272247 : Nat.Prime 7996272247 := by
  apply lucas_primality 7996272247 (3 : ZMod 7996272247)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (31, 1), (754223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (31, 1), (754223, 1)] : List FactorBlock).map factorBlockValue).prod) = 7996272247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_754223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7996272247) ^ 3998136123 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7996272247) ^ 2665424082 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7996272247) ^ 420856434 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7996272247) ^ 257944266 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7996272247) ^ 10602 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_8386731757 : Nat.Prime 8386731757 := by
  apply lucas_primality 8386731757 (2 : ZMod 8386731757)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (17920367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (17920367, 1)] : List FactorBlock).map factorBlockValue).prod) = 8386731757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_17920367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8386731757) ^ 4193365878 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8386731757) ^ 2795577252 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8386731757) ^ 645133212 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8386731757) ^ 468 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_9023609489 : Nat.Prime 9023609489 := by
  apply lucas_primality 9023609489 (3 : ZMod 9023609489)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (563975593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (563975593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9023609489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_563975593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 9023609489) ^ 4511804744 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9023609489) ^ 16 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_9159367771 : Nat.Prime 9159367771 := by
  apply lucas_primality 9159367771 (3 : ZMod 9159367771)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (61, 1), (238339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (61, 1), (238339, 1)] : List FactorBlock).map factorBlockValue).prod) = 9159367771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_61
      · exact prime_oneHundredTwoCV_238339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9159367771) ^ 4579683885 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9159367771) ^ 3053122590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9159367771) ^ 1831873554 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9159367771) ^ 1308481110 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9159367771) ^ 150153570 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9159367771) ^ 38430 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_10328185009 : Nat.Prime 10328185009 := by
  apply lucas_primality 10328185009 (11 : ZMod 10328185009)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (71723507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (71723507, 1)] : List FactorBlock).map factorBlockValue).prod) = 10328185009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_71723507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 10328185009) ^ 5164092504 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10328185009) ^ 3442728336 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10328185009) ^ 144 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_11723363339 : Nat.Prime 11723363339 := by
  apply lucas_primality 11723363339 (2 : ZMod 11723363339)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (263, 1), (128831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (263, 1), (128831, 1)] : List FactorBlock).map factorBlockValue).prod) = 11723363339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_173
      · exact prime_oneHundredTwoCV_263
      · exact prime_oneHundredTwoCV_128831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11723363339) ^ 5861681669 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11723363339) ^ 67765106 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11723363339) ^ 44575526 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11723363339) ^ 90998 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_11817109933 : Nat.Prime 11817109933 := by
  apply lucas_primality 11817109933 (5 : ZMod 11817109933)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (3504481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (3504481, 1)] : List FactorBlock).map factorBlockValue).prod) = 11817109933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_281
      · exact prime_oneHundredTwoCV_3504481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11817109933) ^ 5908554966 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11817109933) ^ 3939036644 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11817109933) ^ 42053772 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11817109933) ^ 3372 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_11830386719 : Nat.Prime 11830386719 := by
  apply lucas_primality 11830386719 (7 : ZMod 11830386719)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (190812689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (190812689, 1)] : List FactorBlock).map factorBlockValue).prod) = 11830386719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_190812689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 11830386719) ^ 5915193359 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 11830386719) ^ 381625378 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 11830386719) ^ 62 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_11834770069 : Nat.Prime 11834770069 := by
  apply lucas_primality 11834770069 (2 : ZMod 11834770069)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (29885783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (29885783, 1)] : List FactorBlock).map factorBlockValue).prod) = 11834770069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_29885783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11834770069) ^ 5917385034 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11834770069) ^ 3944923356 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11834770069) ^ 1075888188 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11834770069) ^ 396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_12272641099 : Nat.Prime 12272641099 := by
  apply lucas_primality 12272641099 (2 : ZMod 12272641099)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (101, 1), (139, 1), (2749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (101, 1), (139, 1), (2749, 1)] : List FactorBlock).map factorBlockValue).prod) = 12272641099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_53
      · exact prime_oneHundredTwoCV_101
      · exact prime_oneHundredTwoCV_139
      · exact prime_oneHundredTwoCV_2749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12272641099) ^ 6136320549 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12272641099) ^ 4090880366 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12272641099) ^ 231559266 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12272641099) ^ 121511298 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12272641099) ^ 88292382 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12272641099) ^ 4464402 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13439966713 : Nat.Prime 13439966713 := by
  apply lucas_primality 13439966713 (7 : ZMod 13439966713)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (139, 1), (138923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (139, 1), (138923, 1)] : List FactorBlock).map factorBlockValue).prod) = 13439966713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_139
      · exact prime_oneHundredTwoCV_138923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13439966713) ^ 6719983356 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13439966713) ^ 4479988904 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13439966713) ^ 463447128 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13439966713) ^ 96690408 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13439966713) ^ 96744 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13504303997 : Nat.Prime 13504303997 := by
  apply lucas_primality 13504303997 (2 : ZMod 13504303997)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (239, 1), (614167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (239, 1), (614167, 1)] : List FactorBlock).map factorBlockValue).prod) = 13504303997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_239
      · exact prime_oneHundredTwoCV_614167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13504303997) ^ 6752151998 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13504303997) ^ 587143652 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13504303997) ^ 56503364 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13504303997) ^ 21988 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13815294133 : Nat.Prime 13815294133 := by
  apply lucas_primality 13815294133 (2 : ZMod 13815294133)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1151274511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1151274511, 1)] : List FactorBlock).map factorBlockValue).prod) = 13815294133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_1151274511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13815294133) ^ 6907647066 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13815294133) ^ 4605098044 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13815294133) ^ 12 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_14229736561 : Nat.Prime 14229736561 := by
  apply lucas_primality 14229736561 (7 : ZMod 14229736561)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 1), (13, 1), (31, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 1), (13, 1), (31, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) = 14229736561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_5449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14229736561) ^ 7114868280 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14229736561) ^ 4743245520 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14229736561) ^ 2845947312 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14229736561) ^ 1094595120 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14229736561) ^ 459023760 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14229736561) ^ 2611440 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_17371489481 : Nat.Prime 17371489481 := by
  apply lucas_primality 17371489481 (3 : ZMod 17371489481)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (181, 1), (293, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (181, 1), (293, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 17371489481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_181
      · exact prime_oneHundredTwoCV_293
      · exact prime_oneHundredTwoCV_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17371489481) ^ 8685744740 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17371489481) ^ 3474297896 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17371489481) ^ 914288920 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17371489481) ^ 95975080 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17371489481) ^ 59288360 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17371489481) ^ 40305080 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_18047218979 : Nat.Prime 18047218979 := by
  apply lucas_primality 18047218979 (2 : ZMod 18047218979)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9023609489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9023609489, 1)] : List FactorBlock).map factorBlockValue).prod) = 18047218979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_9023609489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 18047218979) ^ 9023609489 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18047218979) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_18890247209 : Nat.Prime 18890247209 := by
  apply lucas_primality 18890247209 (3 : ZMod 18890247209)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (23, 2), (127, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (23, 2), (127, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) = 18890247209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_127
      · exact prime_oneHundredTwoCV_5021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18890247209) ^ 9445123604 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18890247209) ^ 2698606744 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18890247209) ^ 821315096 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18890247209) ^ 148742104 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18890247209) ^ 3762248 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_20197070633 : Nat.Prime 20197070633 := by
  apply lucas_primality 20197070633 (3 : ZMod 20197070633)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4091, 1), (617119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4091, 1), (617119, 1)] : List FactorBlock).map factorBlockValue).prod) = 20197070633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_4091
      · exact prime_oneHundredTwoCV_617119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20197070633) ^ 10098535316 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20197070633) ^ 4936952 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20197070633) ^ 32728 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_27089954753 : Nat.Prime 27089954753 := by
  apply lucas_primality 27089954753 (3 : ZMod 27089954753)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (47, 1), (137, 1), (9391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (47, 1), (137, 1), (9391, 1)] : List FactorBlock).map factorBlockValue).prod) = 27089954753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_47
      · exact prime_oneHundredTwoCV_137
      · exact prime_oneHundredTwoCV_9391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27089954753) ^ 13544977376 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 27089954753) ^ 3869993536 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 27089954753) ^ 576382016 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 27089954753) ^ 197736896 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 27089954753) ^ 2884672 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_28929483469 : Nat.Prime 28929483469 := by
  apply lucas_primality 28929483469 (6 : ZMod 28929483469)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (263, 1), (3055501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (263, 1), (3055501, 1)] : List FactorBlock).map factorBlockValue).prod) = 28929483469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_263
      · exact prime_oneHundredTwoCV_3055501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 28929483469) ^ 14464741734 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 28929483469) ^ 9643161156 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 28929483469) ^ 109998036 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 28929483469) ^ 9468 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_29795121799 : Nat.Prime 29795121799 := by
  apply lucas_primality 29795121799 (3 : ZMod 29795121799)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (307, 1), (1244263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (307, 1), (1244263, 1)] : List FactorBlock).map factorBlockValue).prod) = 29795121799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_307
      · exact prime_oneHundredTwoCV_1244263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29795121799) ^ 14897560899 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29795121799) ^ 9931707266 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29795121799) ^ 2291932446 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29795121799) ^ 97052514 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29795121799) ^ 23946 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_31954485259 : Nat.Prime 31954485259 := by
  apply lucas_primality 31954485259 (2 : ZMod 31954485259)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (29, 1), (295727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (29, 1), (295727, 1)] : List FactorBlock).map factorBlockValue).prod) = 31954485259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_295727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31954485259) ^ 15977242629 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31954485259) ^ 10651495086 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31954485259) ^ 1389325446 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31954485259) ^ 1101878802 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31954485259) ^ 108054 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_33167531653 : Nat.Prime 33167531653 := by
  apply lucas_primality 33167531653 (2 : ZMod 33167531653)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (53, 1), (97, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (53, 1), (97, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) = 33167531653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_53
      · exact prime_oneHundredTwoCV_97
      · exact prime_oneHundredTwoCV_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33167531653) ^ 16583765826 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167531653) ^ 11055843884 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167531653) ^ 1143707988 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167531653) ^ 625802484 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167531653) ^ 341933316 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167531653) ^ 1789068 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_35326802131 : Nat.Prime 35326802131 := by
  apply lucas_primality 35326802131 (11 : ZMod 35326802131)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1177560071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1177560071, 1)] : List FactorBlock).map factorBlockValue).prod) = 35326802131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_1177560071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 35326802131) ^ 17663401065 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 35326802131) ^ 11775600710 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 35326802131) ^ 7065360426 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 35326802131) ^ 30 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_36477312343 : Nat.Prime 36477312343 := by
  apply lucas_primality 36477312343 (5 : ZMod 36477312343)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (19423489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (19423489, 1)] : List FactorBlock).map factorBlockValue).prod) = 36477312343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_313
      · exact prime_oneHundredTwoCV_19423489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36477312343) ^ 18238656171 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 36477312343) ^ 12159104114 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 36477312343) ^ 116540934 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 36477312343) ^ 1878 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_40267055753 : Nat.Prime 40267055753 := by
  apply lucas_primality 40267055753 (3 : ZMod 40267055753)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 4), (11, 1), (190579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 4), (11, 1), (190579, 1)] : List FactorBlock).map factorBlockValue).prod) = 40267055753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_190579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40267055753) ^ 20133527876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40267055753) ^ 5752436536 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40267055753) ^ 3660641432 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40267055753) ^ 211288 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_50290613167 : Nat.Prime 50290613167 := by
  apply lucas_primality 50290613167 (3 : ZMod 50290613167)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (83, 1), (1711613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (83, 1), (1711613, 1)] : List FactorBlock).map factorBlockValue).prod) = 50290613167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_59
      · exact prime_oneHundredTwoCV_83
      · exact prime_oneHundredTwoCV_1711613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50290613167) ^ 25145306583 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50290613167) ^ 16763537722 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50290613167) ^ 852383274 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50290613167) ^ 605911002 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50290613167) ^ 29382 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_61155367771 : Nat.Prime 61155367771 := by
  apply lucas_primality 61155367771 (11 : ZMod 61155367771)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (1049, 1), (39659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (1049, 1), (39659, 1)] : List FactorBlock).map factorBlockValue).prod) = 61155367771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_1049
      · exact prime_oneHundredTwoCV_39659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 61155367771) ^ 30577683885 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 61155367771) ^ 20385122590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 61155367771) ^ 12231073554 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 61155367771) ^ 8736481110 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 61155367771) ^ 58298730 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 61155367771) ^ 1542030 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_80731259207 : Nat.Prime 80731259207 := by
  apply lucas_primality 80731259207 (5 : ZMod 80731259207)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3105048431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3105048431, 1)] : List FactorBlock).map factorBlockValue).prod) = 80731259207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_3105048431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 80731259207) ^ 40365629603 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 80731259207) ^ 6210096862 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 80731259207) ^ 26 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_87408271387 : Nat.Prime 87408271387 := by
  apply lucas_primality 87408271387 (3 : ZMod 87408271387)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1931, 1), (2514767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1931, 1), (2514767, 1)] : List FactorBlock).map factorBlockValue).prod) = 87408271387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_1931
      · exact prime_oneHundredTwoCV_2514767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87408271387) ^ 43704135693 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87408271387) ^ 29136090462 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87408271387) ^ 45265806 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87408271387) ^ 34758 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_126211710817 : Nat.Prime 126211710817 := by
  apply lucas_primality 126211710817 (5 : ZMod 126211710817)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (146078369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (146078369, 1)] : List FactorBlock).map factorBlockValue).prod) = 126211710817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_146078369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 126211710817) ^ 63105855408 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 126211710817) ^ 42070570272 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 126211710817) ^ 864 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_132534287227 : Nat.Prime 132534287227 := by
  apply lucas_primality 132534287227 (11 : ZMod 132534287227)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (97, 1), (499, 1), (13829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (97, 1), (499, 1), (13829, 1)] : List FactorBlock).map factorBlockValue).prod) = 132534287227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_97
      · exact prime_oneHundredTwoCV_499
      · exact prime_oneHundredTwoCV_13829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 132534287227) ^ 66267143613 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 132534287227) ^ 44178095742 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 132534287227) ^ 12048571566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 132534287227) ^ 1366332858 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 132534287227) ^ 265599774 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 132534287227) ^ 9583794 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_140344917521 : Nat.Prime 140344917521 := by
  apply lucas_primality 140344917521 (6 : ZMod 140344917521)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (10427, 1), (168247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (10427, 1), (168247, 1)] : List FactorBlock).map factorBlockValue).prod) = 140344917521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_10427
      · exact prime_oneHundredTwoCV_168247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 140344917521) ^ 70172458760 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 140344917521) ^ 28068983504 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 140344917521) ^ 13459760 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 140344917521) ^ 834160 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_145562871347 : Nat.Prime 145562871347 := by
  apply lucas_primality 145562871347 (2 : ZMod 145562871347)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (223, 1), (8820923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (223, 1), (8820923, 1)] : List FactorBlock).map factorBlockValue).prod) = 145562871347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_223
      · exact prime_oneHundredTwoCV_8820923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 145562871347) ^ 72781435673 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145562871347) ^ 3934131658 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145562871347) ^ 652748302 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145562871347) ^ 16502 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_177445594769 : Nat.Prime 177445594769 := by
  apply lucas_primality 177445594769 (3 : ZMod 177445594769)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (149, 1), (1723, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (149, 1), (1723, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) = 177445594769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_149
      · exact prime_oneHundredTwoCV_1723
      · exact prime_oneHundredTwoCV_3323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 177445594769) ^ 88722797384 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 177445594769) ^ 13649661136 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 177445594769) ^ 1190910032 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 177445594769) ^ 102986416 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 177445594769) ^ 53399216 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_201009095291 : Nat.Prime 201009095291 := by
  apply lucas_primality 201009095291 (2 : ZMod 201009095291)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (28393, 1), (707953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (28393, 1), (707953, 1)] : List FactorBlock).map factorBlockValue).prod) = 201009095291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_28393
      · exact prime_oneHundredTwoCV_707953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201009095291) ^ 100504547645 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 201009095291) ^ 40201819058 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 201009095291) ^ 7079530 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 201009095291) ^ 283930 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_230693630879 : Nat.Prime 230693630879 := by
  apply lucas_primality 230693630879 (19 : ZMod 230693630879)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3089, 1), (37341151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3089, 1), (37341151, 1)] : List FactorBlock).map factorBlockValue).prod) = 230693630879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3089
      · exact prime_oneHundredTwoCV_37341151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 230693630879) ^ 115346815439 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 230693630879) ^ 74682302 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (19 : ZMod 230693630879) ^ 6178 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_315835796351 : Nat.Prime 315835796351 := by
  apply lucas_primality 315835796351 (11 : ZMod 315835796351)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (332458733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (332458733, 1)] : List FactorBlock).map factorBlockValue).prod) = 315835796351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_332458733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 315835796351) ^ 157917898175 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 315835796351) ^ 63167159270 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 315835796351) ^ 16622936650 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 315835796351) ^ 950 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_439290400897 : Nat.Prime 439290400897 := by
  apply lucas_primality 439290400897 (10 : ZMod 439290400897)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (127109491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (127109491, 1)] : List FactorBlock).map factorBlockValue).prod) = 439290400897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_127109491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 439290400897) ^ 219645200448 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 439290400897) ^ 146430133632 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 439290400897) ^ 3456 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_446931519889 : Nat.Prime 446931519889 := by
  apply lucas_primality 446931519889 (11 : ZMod 446931519889)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1330153333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1330153333, 1)] : List FactorBlock).map factorBlockValue).prod) = 446931519889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_1330153333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 446931519889) ^ 223465759944 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446931519889) ^ 148977173296 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446931519889) ^ 63847359984 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446931519889) ^ 336 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_447787851443 : Nat.Prime 447787851443 := by
  apply lucas_primality 447787851443 (2 : ZMod 447787851443)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (125371, 1), (1785851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (125371, 1), (1785851, 1)] : List FactorBlock).map factorBlockValue).prod) = 447787851443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_125371
      · exact prime_oneHundredTwoCV_1785851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 447787851443) ^ 223893925721 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 447787851443) ^ 3571702 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 447787851443) ^ 250742 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_460095313949 : Nat.Prime 460095313949 := by
  apply lucas_primality 460095313949 (2 : ZMod 460095313949)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (1138849787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (1138849787, 1)] : List FactorBlock).map factorBlockValue).prod) = 460095313949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_101
      · exact prime_oneHundredTwoCV_1138849787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 460095313949) ^ 230047656974 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 460095313949) ^ 4555399148 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 460095313949) ^ 404 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_461387261759 : Nat.Prime 461387261759 := by
  apply lucas_primality 461387261759 (7 : ZMod 461387261759)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (230693630879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (230693630879, 1)] : List FactorBlock).map factorBlockValue).prod) = 461387261759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_230693630879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 461387261759) ^ 230693630879 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 461387261759) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_578801059477 : Nat.Prime 578801059477 := by
  apply lucas_primality 578801059477 (2 : ZMod 578801059477)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1117, 1), (43181219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1117, 1), (43181219, 1)] : List FactorBlock).map factorBlockValue).prod) = 578801059477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_1117
      · exact prime_oneHundredTwoCV_43181219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 578801059477) ^ 289400529738 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 578801059477) ^ 192933686492 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 578801059477) ^ 518174628 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 578801059477) ^ 13404 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_582532365739 : Nat.Prime 582532365739 := by
  apply lucas_primality 582532365739 (2 : ZMod 582532365739)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (157, 1), (13157437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (157, 1), (13157437, 1)] : List FactorBlock).map factorBlockValue).prod) = 582532365739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_47
      · exact prime_oneHundredTwoCV_157
      · exact prime_oneHundredTwoCV_13157437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 582532365739) ^ 291266182869 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 582532365739) ^ 194177455246 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 582532365739) ^ 12394305654 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 582532365739) ^ 3710397234 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 582532365739) ^ 44274 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_645850073657 : Nat.Prime 645850073657 := by
  apply lucas_primality 645850073657 (3 : ZMod 645850073657)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (80731259207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (80731259207, 1)] : List FactorBlock).map factorBlockValue).prod) = 645850073657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_80731259207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 645850073657) ^ 322925036828 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 645850073657) ^ 8 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_675616527493 : Nat.Prime 675616527493 := by
  apply lucas_primality 675616527493 (2 : ZMod 675616527493)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (31, 1), (359, 1), (523, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (31, 1), (359, 1), (523, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 675616527493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_359
      · exact prime_oneHundredTwoCV_523
      · exact prime_oneHundredTwoCV_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 675616527493) ^ 337808263746 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675616527493) ^ 225205509164 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675616527493) ^ 39742148676 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675616527493) ^ 21794081532 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675616527493) ^ 1881940188 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675616527493) ^ 1291809804 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675616527493) ^ 1187375268 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_803428232083 : Nat.Prime 803428232083 := by
  apply lucas_primality 803428232083 (5 : ZMod 803428232083)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (63599, 1), (300779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (63599, 1), (300779, 1)] : List FactorBlock).map factorBlockValue).prod) = 803428232083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_63599
      · exact prime_oneHundredTwoCV_300779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 803428232083) ^ 401714116041 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428232083) ^ 267809410694 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428232083) ^ 114775461726 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428232083) ^ 12632718 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428232083) ^ 2671158 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1139640037511 : Nat.Prime 1139640037511 := by
  apply lucas_primality 1139640037511 (17 : ZMod 1139640037511)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (983, 1), (8918069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (983, 1), (8918069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139640037511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_983
      · exact prime_oneHundredTwoCV_8918069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1139640037511) ^ 569820018755 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1139640037511) ^ 227928007502 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1139640037511) ^ 87664618270 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1139640037511) ^ 1159348970 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1139640037511) ^ 127790 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1206974716009 : Nat.Prime 1206974716009 := by
  apply lucas_primality 1206974716009 (7 : ZMod 1206974716009)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (50290613167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (50290613167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1206974716009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_50290613167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1206974716009) ^ 603487358004 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1206974716009) ^ 402324905336 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1206974716009) ^ 24 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1214619782413 : Nat.Prime 1214619782413 := by
  apply lucas_primality 1214619782413 (6 : ZMod 1214619782413)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (20963, 1), (112289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (20963, 1), (112289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1214619782413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_43
      · exact prime_oneHundredTwoCV_20963
      · exact prime_oneHundredTwoCV_112289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1214619782413) ^ 607309891206 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1214619782413) ^ 404873260804 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1214619782413) ^ 28246971684 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1214619782413) ^ 57941124 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1214619782413) ^ 10816908 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1225896405133 : Nat.Prime 1225896405133 := by
  apply lucas_primality 1225896405133 (2 : ZMod 1225896405133)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (43, 1), (1423, 1), (12553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (43, 1), (1423, 1), (12553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1225896405133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_43
      · exact prime_oneHundredTwoCV_1423
      · exact prime_oneHundredTwoCV_12553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1225896405133) ^ 612948202566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1225896405133) ^ 408632135044 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1225896405133) ^ 175128057876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1225896405133) ^ 64520863428 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1225896405133) ^ 28509218724 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1225896405133) ^ 861487284 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1225896405133) ^ 97657644 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1274885706047 : Nat.Prime 1274885706047 := by
  apply lucas_primality 1274885706047 (5 : ZMod 1274885706047)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (54949, 1), (11600627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (54949, 1), (11600627, 1)] : List FactorBlock).map factorBlockValue).prod) = 1274885706047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_54949
      · exact prime_oneHundredTwoCV_11600627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1274885706047) ^ 637442853023 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1274885706047) ^ 23201254 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1274885706047) ^ 109898 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1536973767221 : Nat.Prime 1536973767221 := by
  apply lucas_primality 1536973767221 (2 : ZMod 1536973767221)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (151, 1), (508931711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (151, 1), (508931711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1536973767221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_151
      · exact prime_oneHundredTwoCV_508931711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1536973767221) ^ 768486883610 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1536973767221) ^ 307394753444 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1536973767221) ^ 10178634220 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1536973767221) ^ 3020 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1735854243481 : Nat.Prime 1735854243481 := by
  apply lucas_primality 1735854243481 (13 : ZMod 1735854243481)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (15919, 1), (43271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (15919, 1), (43271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1735854243481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_15919
      · exact prime_oneHundredTwoCV_43271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1735854243481) ^ 867927121740 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1735854243481) ^ 578618081160 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1735854243481) ^ 347170848696 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1735854243481) ^ 247979177640 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1735854243481) ^ 109042920 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1735854243481) ^ 40115880 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1752409665397 : Nat.Prime 1752409665397 := by
  apply lucas_primality 1752409665397 (5 : ZMod 1752409665397)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (41, 1), (709, 1), (128813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (41, 1), (709, 1), (128813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1752409665397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_41
      · exact prime_oneHundredTwoCV_709
      · exact prime_oneHundredTwoCV_128813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1752409665397) ^ 876204832698 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1752409665397) ^ 584136555132 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1752409665397) ^ 134800743492 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1752409665397) ^ 42741699156 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1752409665397) ^ 2471663844 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1752409665397) ^ 13604292 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1907602037779 : Nat.Prime 1907602037779 := by
  apply lucas_primality 1907602037779 (2 : ZMod 1907602037779)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (151, 1), (2105521013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (151, 1), (2105521013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1907602037779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_151
      · exact prime_oneHundredTwoCV_2105521013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1907602037779) ^ 953801018889 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1907602037779) ^ 635867345926 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1907602037779) ^ 12633126078 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1907602037779) ^ 906 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3009641931707 : Nat.Prime 3009641931707 := by
  apply lucas_primality 3009641931707 (2 : ZMod 3009641931707)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2129, 1), (706820557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2129, 1), (706820557, 1)] : List FactorBlock).map factorBlockValue).prod) = 3009641931707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_2129
      · exact prime_oneHundredTwoCV_706820557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3009641931707) ^ 1504820965853 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3009641931707) ^ 1413641114 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3009641931707) ^ 4258 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3113538332287 : Nat.Prime 3113538332287 := by
  apply lucas_primality 3113538332287 (3 : ZMod 3113538332287)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13397, 1), (38734273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13397, 1), (38734273, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113538332287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13397
      · exact prime_oneHundredTwoCV_38734273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3113538332287) ^ 1556769166143 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113538332287) ^ 1037846110762 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113538332287) ^ 232405638 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113538332287) ^ 80382 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3382961029001 : Nat.Prime 3382961029001 := by
  apply lucas_primality 3382961029001 (6 : ZMod 3382961029001)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (7, 2), (69040021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (7, 2), (69040021, 1)] : List FactorBlock).map factorBlockValue).prod) = 3382961029001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_69040021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3382961029001) ^ 1691480514500 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3382961029001) ^ 676592205800 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3382961029001) ^ 483280147000 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3382961029001) ^ 49000 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3856951729459 : Nat.Prime 3856951729459 := by
  apply lucas_primality 3856951729459 (2 : ZMod 3856951729459)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (37, 1), (491, 1), (1310527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (37, 1), (491, 1), (1310527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3856951729459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_491
      · exact prime_oneHundredTwoCV_1310527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3856951729459) ^ 1928475864729 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3856951729459) ^ 1285650576486 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3856951729459) ^ 104241938634 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3856951729459) ^ 7855298838 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3856951729459) ^ 2943054 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_4544683376617 : Nat.Prime 4544683376617 := by
  apply lucas_primality 4544683376617 (5 : ZMod 4544683376617)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2591, 1), (24361483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2591, 1), (24361483, 1)] : List FactorBlock).map factorBlockValue).prod) = 4544683376617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_2591
      · exact prime_oneHundredTwoCV_24361483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4544683376617) ^ 2272341688308 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4544683376617) ^ 1514894458872 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4544683376617) ^ 1754026776 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4544683376617) ^ 186552 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_5668037001541 : Nat.Prime 5668037001541 := by
  apply lucas_primality 5668037001541 (2 : ZMod 5668037001541)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (1877, 1), (16776289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (1877, 1), (16776289, 1)] : List FactorBlock).map factorBlockValue).prod) = 5668037001541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_1877
      · exact prime_oneHundredTwoCV_16776289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5668037001541) ^ 2834018500770 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5668037001541) ^ 1889345667180 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5668037001541) ^ 1133607400308 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5668037001541) ^ 3019732020 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5668037001541) ^ 337860 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6145973853241 : Nat.Prime 6145973853241 := by
  apply lucas_primality 6145973853241 (11 : ZMod 6145973853241)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (17, 1), (59, 1), (3927943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (17, 1), (59, 1), (3927943, 1)] : List FactorBlock).map factorBlockValue).prod) = 6145973853241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_59
      · exact prime_oneHundredTwoCV_3927943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6145973853241) ^ 3072986926620 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 6145973853241) ^ 2048657951080 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 6145973853241) ^ 1229194770648 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 6145973853241) ^ 472767219480 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 6145973853241) ^ 361527873720 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 6145973853241) ^ 104169048360 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 6145973853241) ^ 1564680 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6210646456541 : Nat.Prime 6210646456541 := by
  apply lucas_primality 6210646456541 (10 : ZMod 6210646456541)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (227, 1), (1367983801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (227, 1), (1367983801, 1)] : List FactorBlock).map factorBlockValue).prod) = 6210646456541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_227
      · exact prime_oneHundredTwoCV_1367983801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 6210646456541) ^ 3105323228270 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 6210646456541) ^ 1242129291308 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 6210646456541) ^ 27359676020 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 6210646456541) ^ 4540 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6568362802951 : Nat.Prime 6568362802951 := by
  apply lucas_primality 6568362802951 (6 : ZMod 6568362802951)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (103, 1), (32702827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (103, 1), (32702827, 1)] : List FactorBlock).map factorBlockValue).prod) = 6568362802951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_103
      · exact prime_oneHundredTwoCV_32702827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6568362802951) ^ 3284181401475 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6568362802951) ^ 2189454267650 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6568362802951) ^ 1313672560590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6568362802951) ^ 505258677150 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6568362802951) ^ 63770512650 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6568362802951) ^ 200850 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_7319488677107 : Nat.Prime 7319488677107 := by
  apply lucas_primality 7319488677107 (2 : ZMod 7319488677107)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3251, 1), (1125728803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3251, 1), (1125728803, 1)] : List FactorBlock).map factorBlockValue).prod) = 7319488677107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3251
      · exact prime_oneHundredTwoCV_1125728803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7319488677107) ^ 3659744338553 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7319488677107) ^ 2251457606 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7319488677107) ^ 6502 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_8078957984159 : Nat.Prime 8078957984159 := by
  apply lucas_primality 8078957984159 (17 : ZMod 8078957984159)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13967, 1), (289215937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13967, 1), (289215937, 1)] : List FactorBlock).map factorBlockValue).prod) = 8078957984159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13967
      · exact prime_oneHundredTwoCV_289215937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 8078957984159) ^ 4039478992079 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 8078957984159) ^ 578431874 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 8078957984159) ^ 27934 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_9134934499139 : Nat.Prime 9134934499139 := by
  apply lucas_primality 9134934499139 (2 : ZMod 9134934499139)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (281, 1), (2322047407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (281, 1), (2322047407, 1)] : List FactorBlock).map factorBlockValue).prod) = 9134934499139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_281
      · exact prime_oneHundredTwoCV_2322047407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9134934499139) ^ 4567467249569 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9134934499139) ^ 1304990642734 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9134934499139) ^ 32508663698 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9134934499139) ^ 3934 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_10309651359577 : Nat.Prime 10309651359577 := by
  apply lucas_primality 10309651359577 (7 : ZMod 10309651359577)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (79, 1), (175405801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (79, 1), (175405801, 1)] : List FactorBlock).map factorBlockValue).prod) = 10309651359577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_79
      · exact prime_oneHundredTwoCV_175405801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10309651359577) ^ 5154825679788 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10309651359577) ^ 3436550453192 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10309651359577) ^ 332569398696 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10309651359577) ^ 130501915944 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10309651359577) ^ 58776 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_10482716828791 : Nat.Prime 10482716828791 := by
  apply lucas_primality 10482716828791 (3 : ZMod 10482716828791)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (181, 1), (659, 1), (976489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (181, 1), (659, 1), (976489, 1)] : List FactorBlock).map factorBlockValue).prod) = 10482716828791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_181
      · exact prime_oneHundredTwoCV_659
      · exact prime_oneHundredTwoCV_976489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10482716828791) ^ 5241358414395 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10482716828791) ^ 3494238942930 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10482716828791) ^ 2096543365758 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10482716828791) ^ 57915562590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10482716828791) ^ 15907005810 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10482716828791) ^ 10735110 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_12218187282907 : Nat.Prime 12218187282907 := by
  apply lucas_primality 12218187282907 (3 : ZMod 12218187282907)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (127, 1), (719, 1), (106703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (127, 1), (719, 1), (106703, 1)] : List FactorBlock).map factorBlockValue).prod) = 12218187282907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_127
      · exact prime_oneHundredTwoCV_719
      · exact prime_oneHundredTwoCV_106703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12218187282907) ^ 6109093641453 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12218187282907) ^ 4072729094302 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12218187282907) ^ 1110744298446 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12218187282907) ^ 643062488574 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12218187282907) ^ 96206199078 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12218187282907) ^ 16993306374 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12218187282907) ^ 114506502 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13052058141151 : Nat.Prime 13052058141151 := by
  apply lucas_primality 13052058141151 (3 : ZMod 13052058141151)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (17, 1), (7589, 1), (32117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (17, 1), (7589, 1), (32117, 1)] : List FactorBlock).map factorBlockValue).prod) = 13052058141151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_7589
      · exact prime_oneHundredTwoCV_32117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13052058141151) ^ 6526029070575 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13052058141151) ^ 4350686047050 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13052058141151) ^ 2610411628230 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13052058141151) ^ 1864579734450 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13052058141151) ^ 767768125950 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13052058141151) ^ 1719865350 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13052058141151) ^ 406390950 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_18849500653133 : Nat.Prime 18849500653133 := by
  apply lucas_primality 18849500653133 (2 : ZMod 18849500653133)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (167, 1), (4219, 1), (94201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (167, 1), (4219, 1), (94201, 1)] : List FactorBlock).map factorBlockValue).prod) = 18849500653133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_71
      · exact prime_oneHundredTwoCV_167
      · exact prime_oneHundredTwoCV_4219
      · exact prime_oneHundredTwoCV_94201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18849500653133) ^ 9424750326566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18849500653133) ^ 265485924692 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18849500653133) ^ 112871261396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18849500653133) ^ 4467765028 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18849500653133) ^ 200098732 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_19211102133317 : Nat.Prime 19211102133317 := by
  apply lucas_primality 19211102133317 (2 : ZMod 19211102133317)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9413, 1), (510227933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9413, 1), (510227933, 1)] : List FactorBlock).map factorBlockValue).prod) = 19211102133317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_9413
      · exact prime_oneHundredTwoCV_510227933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19211102133317) ^ 9605551066658 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211102133317) ^ 2040911732 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211102133317) ^ 37652 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_22645281381097 : Nat.Prime 22645281381097 := by
  apply lucas_primality 22645281381097 (10 : ZMod 22645281381097)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (23, 1), (13933, 1), (267671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (23, 1), (13933, 1), (267671, 1)] : List FactorBlock).map factorBlockValue).prod) = 22645281381097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_13933
      · exact prime_oneHundredTwoCV_267671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 22645281381097) ^ 11322640690548 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 22645281381097) ^ 7548427127032 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 22645281381097) ^ 2058661943736 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 22645281381097) ^ 984577451352 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 22645281381097) ^ 1625298312 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 22645281381097) ^ 84601176 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_23658976647589 : Nat.Prime 23658976647589 := by
  apply lucas_primality 23658976647589 (2 : ZMod 23658976647589)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3217, 1), (612863347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3217, 1), (612863347, 1)] : List FactorBlock).map factorBlockValue).prod) = 23658976647589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_3217
      · exact prime_oneHundredTwoCV_612863347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23658976647589) ^ 11829488323794 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23658976647589) ^ 7886325549196 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23658976647589) ^ 7354360164 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23658976647589) ^ 38604 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_31675393584787 : Nat.Prime 31675393584787 := by
  apply lucas_primality 31675393584787 (2 : ZMod 31675393584787)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (14229736561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (14229736561, 1)] : List FactorBlock).map factorBlockValue).prod) = 31675393584787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_53
      · exact prime_oneHundredTwoCV_14229736561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31675393584787) ^ 15837696792393 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31675393584787) ^ 10558464528262 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31675393584787) ^ 4525056226398 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31675393584787) ^ 597648935562 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31675393584787) ^ 2226 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_40267112616959 : Nat.Prime 40267112616959 := by
  apply lucas_primality 40267112616959 (7 : ZMod 40267112616959)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (61, 1), (17371489481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (61, 1), (17371489481, 1)] : List FactorBlock).map factorBlockValue).prod) = 40267112616959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_61
      · exact prime_oneHundredTwoCV_17371489481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 40267112616959) ^ 20133556308479 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 40267112616959) ^ 2119321716682 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 40267112616959) ^ 660116600278 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 40267112616959) ^ 2318 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_41967244831139 : Nat.Prime 41967244831139 := by
  apply lucas_primality 41967244831139 (2 : ZMod 41967244831139)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1907602037779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1907602037779, 1)] : List FactorBlock).map factorBlockValue).prod) = 41967244831139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_1907602037779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41967244831139) ^ 20983622415569 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 41967244831139) ^ 3815204075558 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 41967244831139) ^ 22 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_50813961734917 : Nat.Prime 50813961734917 := by
  apply lucas_primality 50813961734917 (2 : ZMod 50813961734917)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (191, 1), (7390046791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (191, 1), (7390046791, 1)] : List FactorBlock).map factorBlockValue).prod) = 50813961734917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_191
      · exact prime_oneHundredTwoCV_7390046791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50813961734917) ^ 25406980867458 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50813961734917) ^ 16937987244972 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50813961734917) ^ 266041684476 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50813961734917) ^ 6876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_61459738532411 : Nat.Prime 61459738532411 := by
  apply lucas_primality 61459738532411 (2 : ZMod 61459738532411)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6145973853241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6145973853241, 1)] : List FactorBlock).map factorBlockValue).prod) = 61459738532411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_6145973853241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61459738532411) ^ 30729869266205 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 61459738532411) ^ 12291947706482 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 61459738532411) ^ 10 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_72418482960541 : Nat.Prime 72418482960541 := by
  apply lucas_primality 72418482960541 (2 : ZMod 72418482960541)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1206974716009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1206974716009, 1)] : List FactorBlock).map factorBlockValue).prod) = 72418482960541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_1206974716009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72418482960541) ^ 36209241480270 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 72418482960541) ^ 24139494320180 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 72418482960541) ^ 14483696592108 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 72418482960541) ^ 60 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_76493142362821 : Nat.Prime 76493142362821 := by
  apply lucas_primality 76493142362821 (6 : ZMod 76493142362821)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1274885706047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1274885706047, 1)] : List FactorBlock).map factorBlockValue).prod) = 76493142362821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_1274885706047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 76493142362821) ^ 38246571181410 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 76493142362821) ^ 25497714120940 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 76493142362821) ^ 15298628472564 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 76493142362821) ^ 60 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_78416306825587 : Nat.Prime 78416306825587 := by
  apply lucas_primality 78416306825587 (2 : ZMod 78416306825587)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (409, 1), (31954485259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (409, 1), (31954485259, 1)] : List FactorBlock).map factorBlockValue).prod) = 78416306825587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_409
      · exact prime_oneHundredTwoCV_31954485259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78416306825587) ^ 39208153412793 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78416306825587) ^ 26138768941862 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78416306825587) ^ 191726911554 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78416306825587) ^ 2454 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_80534225233919 : Nat.Prime 80534225233919 := by
  apply lucas_primality 80534225233919 (7 : ZMod 80534225233919)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40267112616959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40267112616959, 1)] : List FactorBlock).map factorBlockValue).prod) = 80534225233919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_40267112616959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 80534225233919) ^ 40267112616959 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 80534225233919) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_95038650333247 : Nat.Prime 95038650333247 := by
  apply lucas_primality 95038650333247 (3 : ZMod 95038650333247)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2447, 1), (6473140603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2447, 1), (6473140603, 1)] : List FactorBlock).map factorBlockValue).prod) = 95038650333247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_2447
      · exact prime_oneHundredTwoCV_6473140603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 95038650333247) ^ 47519325166623 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95038650333247) ^ 31679550111082 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95038650333247) ^ 38838843618 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95038650333247) ^ 14682 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_99670031536351 : Nat.Prime 99670031536351 := by
  apply lucas_primality 99670031536351 (3 : ZMod 99670031536351)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (17, 1), (83, 1), (149, 1), (287321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (17, 1), (83, 1), (149, 1), (287321, 1)] : List FactorBlock).map factorBlockValue).prod) = 99670031536351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_83
      · exact prime_oneHundredTwoCV_149
      · exact prime_oneHundredTwoCV_287321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 99670031536351) ^ 49835015768175 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 33223343845450 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 19934006307270 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 9060911957850 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 5862943031550 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 1200843753450 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 668926386150 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 99670031536351) ^ 346894350 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_108186101438201 : Nat.Prime 108186101438201 := by
  apply lucas_primality 108186101438201 (6 : ZMod 108186101438201)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (43, 1), (103, 1), (122133779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (43, 1), (103, 1), (122133779, 1)] : List FactorBlock).map factorBlockValue).prod) = 108186101438201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_43
      · exact prime_oneHundredTwoCV_103
      · exact prime_oneHundredTwoCV_122133779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 108186101438201) ^ 54093050719100 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 108186101438201) ^ 21637220287640 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 108186101438201) ^ 2515955847400 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 108186101438201) ^ 1050350499400 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (6 : ZMod 108186101438201) ^ 885800 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_126701574339149 : Nat.Prime 126701574339149 := by
  apply lucas_primality 126701574339149 (2 : ZMod 126701574339149)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31675393584787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31675393584787, 1)] : List FactorBlock).map factorBlockValue).prod) = 126701574339149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_31675393584787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 126701574339149) ^ 63350787169574 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 126701574339149) ^ 4 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_141340924460369 : Nat.Prime 141340924460369 := by
  apply lucas_primality 141340924460369 (3 : ZMod 141340924460369)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (12659, 1), (24063043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (12659, 1), (24063043, 1)] : List FactorBlock).map factorBlockValue).prod) = 141340924460369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_12659
      · exact prime_oneHundredTwoCV_24063043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 141340924460369) ^ 70670462230184 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 141340924460369) ^ 4873824981392 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 141340924460369) ^ 11165251952 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 141340924460369) ^ 5873776 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_216087740160283 : Nat.Prime 216087740160283 := by
  apply lucas_primality 216087740160283 (3 : ZMod 216087740160283)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (67, 1), (947, 1), (1013, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (67, 1), (947, 1), (1013, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 216087740160283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_67
      · exact prime_oneHundredTwoCV_947
      · exact prime_oneHundredTwoCV_1013
      · exact prime_oneHundredTwoCV_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 216087740160283) ^ 108043870080141 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216087740160283) ^ 72029246720094 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216087740160283) ^ 3225190151646 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216087740160283) ^ 228181351806 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216087740160283) ^ 213314649714 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216087740160283) ^ 10412361594 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_278638985960059 : Nat.Prime 278638985960059 := by
  apply lucas_primality 278638985960059 (2 : ZMod 278638985960059)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8233, 1), (5640693671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8233, 1), (5640693671, 1)] : List FactorBlock).map factorBlockValue).prod) = 278638985960059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_8233
      · exact prime_oneHundredTwoCV_5640693671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 278638985960059) ^ 139319492980029 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 278638985960059) ^ 92879661986686 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 278638985960059) ^ 33844162026 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 278638985960059) ^ 49398 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_330549465912203 : Nat.Prime 330549465912203 := by
  apply lucas_primality 330549465912203 (2 : ZMod 330549465912203)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (3833, 1), (329151887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (3833, 1), (329151887, 1)] : List FactorBlock).map factorBlockValue).prod) = 330549465912203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_131
      · exact prime_oneHundredTwoCV_3833
      · exact prime_oneHundredTwoCV_329151887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 330549465912203) ^ 165274732956101 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330549465912203) ^ 2523278365742 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330549465912203) ^ 86237794394 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330549465912203) ^ 1004246 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_374838159680723 : Nat.Prime 374838159680723 := by
  apply lucas_primality 374838159680723 (2 : ZMod 374838159680723)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26731, 1), (7011300731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26731, 1), (7011300731, 1)] : List FactorBlock).map factorBlockValue).prod) = 374838159680723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_26731
      · exact prime_oneHundredTwoCV_7011300731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 374838159680723) ^ 187419079840361 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 374838159680723) ^ 14022601462 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 374838159680723) ^ 53462 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_459785396206571 : Nat.Prime 459785396206571 := by
  apply lucas_primality 459785396206571 (2 : ZMod 459785396206571)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (6568362802951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (6568362802951, 1)] : List FactorBlock).map factorBlockValue).prod) = 459785396206571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_6568362802951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 459785396206571) ^ 229892698103285 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 459785396206571) ^ 91957079241314 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 459785396206571) ^ 65683628029510 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 459785396206571) ^ 70 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_478910090729501 : Nat.Prime 478910090729501 := by
  apply lucas_primality 478910090729501 (2 : ZMod 478910090729501)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (47, 1), (157, 1), (199, 1), (652279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (47, 1), (157, 1), (199, 1), (652279, 1)] : List FactorBlock).map factorBlockValue).prod) = 478910090729501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_47
      · exact prime_oneHundredTwoCV_157
      · exact prime_oneHundredTwoCV_199
      · exact prime_oneHundredTwoCV_652279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 478910090729501) ^ 239455045364750 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478910090729501) ^ 95782018145900 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478910090729501) ^ 10189576398500 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478910090729501) ^ 3050382743500 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478910090729501) ^ 2406583370500 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478910090729501) ^ 734210500 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_498951395668307 : Nat.Prime 498951395668307 := by
  apply lucas_primality 498951395668307 (5 : ZMod 498951395668307)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4457, 1), (7996272247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4457, 1), (7996272247, 1)] : List FactorBlock).map factorBlockValue).prod) = 498951395668307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_4457
      · exact prime_oneHundredTwoCV_7996272247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 498951395668307) ^ 249475697834153 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 498951395668307) ^ 71278770809758 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 498951395668307) ^ 111947811458 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 498951395668307) ^ 62398 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_559694274621637 : Nat.Prime 559694274621637 := by
  apply lucas_primality 559694274621637 (23 : ZMod 559694274621637)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (509, 1), (1190038771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (509, 1), (1190038771, 1)] : List FactorBlock).map factorBlockValue).prod) = 559694274621637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_509
      · exact prime_oneHundredTwoCV_1190038771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 559694274621637) ^ 279847137310818 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (23 : ZMod 559694274621637) ^ 186564758207212 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (23 : ZMod 559694274621637) ^ 79956324945948 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (23 : ZMod 559694274621637) ^ 50881297692876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (23 : ZMod 559694274621637) ^ 1099595824404 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (23 : ZMod 559694274621637) ^ 470316 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_566012818604459 : Nat.Prime 566012818604459 := by
  apply lucas_primality 566012818604459 (2 : ZMod 566012818604459)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (1214619782413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (1214619782413, 1)] : List FactorBlock).map factorBlockValue).prod) = 566012818604459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_233
      · exact prime_oneHundredTwoCV_1214619782413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 566012818604459) ^ 283006409302229 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 566012818604459) ^ 2429239564826 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 566012818604459) ^ 466 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_570231901999483 : Nat.Prime 570231901999483 := by
  apply lucas_primality 570231901999483 (2 : ZMod 570231901999483)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (95038650333247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (95038650333247, 1)] : List FactorBlock).map factorBlockValue).prod) = 570231901999483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_95038650333247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 570231901999483) ^ 285115950999741 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 570231901999483) ^ 190077300666494 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 570231901999483) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_957820181459003 : Nat.Prime 957820181459003 := by
  apply lucas_primality 957820181459003 (2 : ZMod 957820181459003)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (478910090729501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (478910090729501, 1)] : List FactorBlock).map factorBlockValue).prod) = 957820181459003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_478910090729501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 957820181459003) ^ 478910090729501 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 957820181459003) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_981058698410291 : Nat.Prime 981058698410291 := by
  apply lucas_primality 981058698410291 (2 : ZMod 981058698410291)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (3382961029001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (3382961029001, 1)] : List FactorBlock).map factorBlockValue).prod) = 981058698410291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_3382961029001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 981058698410291) ^ 490529349205145 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 981058698410291) ^ 196211739682058 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 981058698410291) ^ 33829610290010 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 981058698410291) ^ 290 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1209904525158163 : Nat.Prime 1209904525158163 := by
  apply lucas_primality 1209904525158163 (2 : ZMod 1209904525158163)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (8123, 1), (1079333263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (8123, 1), (1079333263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1209904525158163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_8123
      · exact prime_oneHundredTwoCV_1079333263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1209904525158163) ^ 604952262579081 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1209904525158163) ^ 403301508386054 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1209904525158163) ^ 52604544572094 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1209904525158163) ^ 148947990294 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1209904525158163) ^ 1120974 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1244855055247759 : Nat.Prime 1244855055247759 := by
  apply lucas_primality 1244855055247759 (3 : ZMod 1244855055247759)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (89, 1), (239, 1), (3631, 1), (298477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (89, 1), (239, 1), (3631, 1), (298477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244855055247759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_89
      · exact prime_oneHundredTwoCV_239
      · exact prime_oneHundredTwoCV_3631
      · exact prime_oneHundredTwoCV_298477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1244855055247759) ^ 622427527623879 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244855055247759) ^ 414951685082586 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244855055247759) ^ 13987135452222 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244855055247759) ^ 5208598557522 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244855055247759) ^ 342840830418 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244855055247759) ^ 4170690054 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1294457005104863 : Nat.Prime 1294457005104863 := by
  apply lucas_primality 1294457005104863 (5 : ZMod 1294457005104863)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6779, 1), (36739, 1), (2598751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6779, 1), (36739, 1), (2598751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1294457005104863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_6779
      · exact prime_oneHundredTwoCV_36739
      · exact prime_oneHundredTwoCV_2598751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1294457005104863) ^ 647228502552431 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1294457005104863) ^ 190951025978 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1294457005104863) ^ 35233866058 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1294457005104863) ^ 498107362 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1342389835013681 : Nat.Prime 1342389835013681 := by
  apply lucas_primality 1342389835013681 (7 : ZMod 1342389835013681)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (109, 1), (80077, 1), (1922447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (109, 1), (80077, 1), (1922447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342389835013681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_109
      · exact prime_oneHundredTwoCV_80077
      · exact prime_oneHundredTwoCV_1922447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1342389835013681) ^ 671194917506840 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1342389835013681) ^ 268477967002736 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1342389835013681) ^ 12315503073520 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1342389835013681) ^ 16763737840 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1342389835013681) ^ 698271440 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2615013272573203 : Nat.Prime 2615013272573203 := by
  apply lucas_primality 2615013272573203 (2 : ZMod 2615013272573203)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (3856951729459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (3856951729459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2615013272573203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_113
      · exact prime_oneHundredTwoCV_3856951729459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2615013272573203) ^ 1307506636286601 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2615013272573203) ^ 871671090857734 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2615013272573203) ^ 23141710376754 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2615013272573203) ^ 678 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2657554012231133 : Nat.Prime 2657554012231133 := by
  apply lucas_primality 2657554012231133 (2 : ZMod 2657554012231133)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11317, 1), (8386731757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11317, 1), (8386731757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2657554012231133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_11317
      · exact prime_oneHundredTwoCV_8386731757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2657554012231133) ^ 1328777006115566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2657554012231133) ^ 379650573175876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2657554012231133) ^ 234828489196 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2657554012231133) ^ 316876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2984564659794131 : Nat.Prime 2984564659794131 := by
  apply lucas_primality 2984564659794131 (2 : ZMod 2984564659794131)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (470783, 1), (90565373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (470783, 1), (90565373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2984564659794131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_470783
      · exact prime_oneHundredTwoCV_90565373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2984564659794131) ^ 1492282329897065 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984564659794131) ^ 596912931958826 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984564659794131) ^ 426366379970590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984564659794131) ^ 6339576110 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984564659794131) ^ 32954810 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3232828518956791 : Nat.Prime 3232828518956791 := by
  apply lucas_primality 3232828518956791 (3 : ZMod 3232828518956791)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (31, 1), (14243, 1), (18773917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (31, 1), (14243, 1), (18773917, 1)] : List FactorBlock).map factorBlockValue).prod) = 3232828518956791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_14243
      · exact prime_oneHundredTwoCV_18773917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3232828518956791) ^ 1616414259478395 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3232828518956791) ^ 1077609506318930 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3232828518956791) ^ 646565703791358 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3232828518956791) ^ 248679116842830 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3232828518956791) ^ 104284790934090 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3232828518956791) ^ 226976656530 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3232828518956791) ^ 172197870 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3586169597226101 : Nat.Prime 3586169597226101 := by
  apply lucas_primality 3586169597226101 (2 : ZMod 3586169597226101)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (23, 1), (31, 1), (709, 1), (70940633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (23, 1), (31, 1), (709, 1), (70940633, 1)] : List FactorBlock).map factorBlockValue).prod) = 3586169597226101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_709
      · exact prime_oneHundredTwoCV_70940633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3586169597226101) ^ 1793084798613050 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3586169597226101) ^ 717233919445220 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3586169597226101) ^ 155920417270700 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3586169597226101) ^ 115682890233100 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3586169597226101) ^ 5058067132900 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3586169597226101) ^ 50551700 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_4638340076889133 : Nat.Prime 4638340076889133 := by
  apply lucas_primality 4638340076889133 (2 : ZMod 4638340076889133)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (3079, 1), (9491, 1), (489887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (3079, 1), (9491, 1), (489887, 1)] : List FactorBlock).map factorBlockValue).prod) = 4638340076889133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_3079
      · exact prime_oneHundredTwoCV_9491
      · exact prime_oneHundredTwoCV_489887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4638340076889133) ^ 2319170038444566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4638340076889133) ^ 1546113358963044 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4638340076889133) ^ 1506443675508 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4638340076889133) ^ 488709311652 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4638340076889133) ^ 9468183636 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_9837134014581169 : Nat.Prime 9837134014581169 := by
  apply lucas_primality 9837134014581169 (17 : ZMod 9837134014581169)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (571, 1), (18890247209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (571, 1), (18890247209, 1)] : List FactorBlock).map factorBlockValue).prod) = 9837134014581169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_571
      · exact prime_oneHundredTwoCV_18890247209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 9837134014581169) ^ 4918567007290584 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 9837134014581169) ^ 3279044671527056 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 9837134014581169) ^ 517743895504272 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 9837134014581169) ^ 17227905454608 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 9837134014581169) ^ 520752 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13034663486071679 : Nat.Prime 13034663486071679 := by
  apply lucas_primality 13034663486071679 (7 : ZMod 13034663486071679)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (339187, 1), (91935733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (339187, 1), (91935733, 1)] : List FactorBlock).map factorBlockValue).prod) = 13034663486071679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_339187
      · exact prime_oneHundredTwoCV_91935733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13034663486071679) ^ 6517331743035839 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13034663486071679) ^ 1184969407824698 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13034663486071679) ^ 686034920319562 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13034663486071679) ^ 38429136394 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 13034663486071679) ^ 141780166 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13740286455772937 : Nat.Prime 13740286455772937 := by
  apply lucas_primality 13740286455772937 (3 : ZMod 13740286455772937)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3733, 1), (460095313949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3733, 1), (460095313949, 1)] : List FactorBlock).map factorBlockValue).prod) = 13740286455772937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3733
      · exact prime_oneHundredTwoCV_460095313949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13740286455772937) ^ 6870143227886468 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13740286455772937) ^ 3680762511592 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13740286455772937) ^ 29864 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_22597909673617721 : Nat.Prime 22597909673617721 := by
  apply lucas_primality 22597909673617721 (3 : ZMod 22597909673617721)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (113, 1), (11941, 1), (32206667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (113, 1), (11941, 1), (32206667, 1)] : List FactorBlock).map factorBlockValue).prod) = 22597909673617721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_113
      · exact prime_oneHundredTwoCV_11941
      · exact prime_oneHundredTwoCV_32206667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22597909673617721) ^ 11298954836808860 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 22597909673617721) ^ 4519581934723544 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 22597909673617721) ^ 1738300744124440 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 22597909673617721) ^ 199981501536440 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 22597909673617721) ^ 1892463752920 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 22597909673617721) ^ 701653160 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_36333096528589607 : Nat.Prime 36333096528589607 := by
  apply lucas_primality 36333096528589607 (5 : ZMod 36333096528589607)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1733, 1), (10482716828791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1733, 1), (10482716828791, 1)] : List FactorBlock).map factorBlockValue).prod) = 36333096528589607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_1733
      · exact prime_oneHundredTwoCV_10482716828791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 36333096528589607) ^ 18166548264294803 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 36333096528589607) ^ 20965433657582 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 36333096528589607) ^ 3466 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_36799082128594603 : Nat.Prime 36799082128594603 := by
  apply lucas_primality 36799082128594603 (3 : ZMod 36799082128594603)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (21191, 1), (58099, 1), (553507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (21191, 1), (58099, 1), (553507, 1)] : List FactorBlock).map factorBlockValue).prod) = 36799082128594603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_21191
      · exact prime_oneHundredTwoCV_58099
      · exact prime_oneHundredTwoCV_553507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36799082128594603) ^ 18399541064297301 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36799082128594603) ^ 12266360709531534 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36799082128594603) ^ 1736542972422 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36799082128594603) ^ 633385809198 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36799082128594603) ^ 66483499086 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_89436232175885993 : Nat.Prime 89436232175885993 := by
  apply lucas_primality 89436232175885993 (3 : ZMod 89436232175885993)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (347, 1), (141199, 1), (2352289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (347, 1), (141199, 1), (2352289, 1)] : List FactorBlock).map factorBlockValue).prod) = 89436232175885993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_97
      · exact prime_oneHundredTwoCV_347
      · exact prime_oneHundredTwoCV_141199
      · exact prime_oneHundredTwoCV_2352289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89436232175885993) ^ 44718116087942996 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 89436232175885993) ^ 922023012122536 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 89436232175885993) ^ 257741303100536 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 89436232175885993) ^ 633405563608 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 89436232175885993) ^ 38020937128 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_150095823575726593 : Nat.Prime 150095823575726593 := by
  apply lucas_primality 150095823575726593 (5 : ZMod 150095823575726593)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (31643, 1), (1029386543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (31643, 1), (1029386543, 1)] : List FactorBlock).map factorBlockValue).prod) = 150095823575726593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_31643
      · exact prime_oneHundredTwoCV_1029386543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 150095823575726593) ^ 75047911787863296 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 150095823575726593) ^ 50031941191908864 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 150095823575726593) ^ 4743413190144 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 150095823575726593) ^ 145810944 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_169755614485484369 : Nat.Prime 169755614485484369 := by
  apply lucas_primality 169755614485484369 (3 : ZMod 169755614485484369)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (8329157, 1), (115800499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (8329157, 1), (115800499, 1)] : List FactorBlock).map factorBlockValue).prod) = 169755614485484369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_8329157
      · exact prime_oneHundredTwoCV_115800499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 169755614485484369) ^ 84877807242742184 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 169755614485484369) ^ 15432328589589488 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 169755614485484369) ^ 20380887824 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 169755614485484369) ^ 1465931632 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_178769354575065181 : Nat.Prime 178769354575065181 := by
  apply lucas_primality 178769354575065181 (2 : ZMod 178769354575065181)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 2), (10309651359577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 2), (10309651359577, 1)] : List FactorBlock).map factorBlockValue).prod) = 178769354575065181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_10309651359577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178769354575065181) ^ 89384677287532590 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 178769354575065181) ^ 59589784858355060 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 178769354575065181) ^ 35753870915013036 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 178769354575065181) ^ 10515844386768540 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 178769354575065181) ^ 17340 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_216408980372251243 : Nat.Prime 216408980372251243 := by
  apply lucas_primality 216408980372251243 (3 : ZMod 216408980372251243)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (757, 1), (1536973767221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (757, 1), (1536973767221, 1)] : List FactorBlock).map factorBlockValue).prod) = 216408980372251243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_31
      · exact prime_oneHundredTwoCV_757
      · exact prime_oneHundredTwoCV_1536973767221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 216408980372251243) ^ 108204490186125621 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216408980372251243) ^ 72136326790750414 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216408980372251243) ^ 6980934850717782 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216408980372251243) ^ 285877120703106 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 216408980372251243) ^ 140802 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_417450606920021971 : Nat.Prime 417450606920021971 := by
  apply lucas_primality 417450606920021971 (2 : ZMod 417450606920021971)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (4638340076889133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (4638340076889133, 1)] : List FactorBlock).map factorBlockValue).prod) = 417450606920021971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_4638340076889133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 417450606920021971) ^ 208725303460010985 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 417450606920021971) ^ 139150202306673990 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 417450606920021971) ^ 83490121384004394 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 417450606920021971) ^ 90 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_573061713053950177 : Nat.Prime 573061713053950177 := by
  apply lucas_primality 573061713053950177 (5 : ZMod 573061713053950177)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 2), (3673, 1), (33167531653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 2), (3673, 1), (33167531653, 1)] : List FactorBlock).map factorBlockValue).prod) = 573061713053950177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_3673
      · exact prime_oneHundredTwoCV_33167531653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 573061713053950177) ^ 286530856526975088 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 573061713053950177) ^ 191020571017983392 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 573061713053950177) ^ 81865959007707168 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 573061713053950177) ^ 156020068895712 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 573061713053950177) ^ 17277792 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_865635921489004973 : Nat.Prime 865635921489004973 := by
  apply lucas_primality 865635921489004973 (2 : ZMod 865635921489004973)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (216408980372251243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (216408980372251243, 1)] : List FactorBlock).map factorBlockValue).prod) = 865635921489004973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_216408980372251243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 865635921489004973) ^ 432817960744502486 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 865635921489004973) ^ 4 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_908487733949756021 : Nat.Prime 908487733949756021 := by
  apply lucas_primality 908487733949756021 (2 : ZMod 908487733949756021)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3469, 1), (1292429, 1), (10131601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3469, 1), (1292429, 1), (10131601, 1)] : List FactorBlock).map factorBlockValue).prod) = 908487733949756021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_3469
      · exact prime_oneHundredTwoCV_1292429
      · exact prime_oneHundredTwoCV_10131601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 908487733949756021) ^ 454243866974878010 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 908487733949756021) ^ 181697546789951204 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 908487733949756021) ^ 261887498976580 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 908487733949756021) ^ 702930477380 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 908487733949756021) ^ 89668724020 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1457061029471741119 : Nat.Prime 1457061029471741119 := by
  apply lucas_primality 1457061029471741119 (3 : ZMod 1457061029471741119)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (353, 1), (38119, 1), (18047218979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (353, 1), (38119, 1), (18047218979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1457061029471741119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_353
      · exact prime_oneHundredTwoCV_38119
      · exact prime_oneHundredTwoCV_18047218979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1457061029471741119) ^ 728530514735870559 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1457061029471741119) ^ 485687009823913706 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1457061029471741119) ^ 4127651641563006 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1457061029471741119) ^ 38224009797522 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1457061029471741119) ^ 80736042 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1546347020427381989 : Nat.Prime 1546347020427381989 := by
  apply lucas_primality 1546347020427381989 (2 : ZMod 1546347020427381989)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (683, 1), (566012818604459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (683, 1), (566012818604459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546347020427381989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_683
      · exact prime_oneHundredTwoCV_566012818604459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1546347020427381989) ^ 773173510213690994 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1546347020427381989) ^ 2264051274417836 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1546347020427381989) ^ 2732 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3622701707592705509 : Nat.Prime 3622701707592705509 := by
  apply lucas_primality 3622701707592705509 (2 : ZMod 3622701707592705509)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (112103, 1), (8078957984159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (112103, 1), (8078957984159, 1)] : List FactorBlock).map factorBlockValue).prod) = 3622701707592705509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_112103
      · exact prime_oneHundredTwoCV_8078957984159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3622701707592705509) ^ 1811350853796352754 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3622701707592705509) ^ 32315831936636 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3622701707592705509) ^ 448412 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6803947973220272533 : Nat.Prime 6803947973220272533 := by
  apply lucas_primality 6803947973220272533 (5 : ZMod 6803947973220272533)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (1867, 1), (13967, 1), (345137173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (1867, 1), (13967, 1), (345137173, 1)] : List FactorBlock).map factorBlockValue).prod) = 6803947973220272533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_1867
      · exact prime_oneHundredTwoCV_13967
      · exact prime_oneHundredTwoCV_345137173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6803947973220272533) ^ 3401973986610136266 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6803947973220272533) ^ 2267982657740090844 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6803947973220272533) ^ 971992567602896076 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6803947973220272533) ^ 3644321356839996 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6803947973220272533) ^ 487144553105196 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6803947973220272533) ^ 19713750084 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13219223366995570511 : Nat.Prime 13219223366995570511 := by
  apply lucas_primality 13219223366995570511 (11 : ZMod 13219223366995570511)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (108193, 1), (12218187282907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (108193, 1), (12218187282907, 1)] : List FactorBlock).map factorBlockValue).prod) = 13219223366995570511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_108193
      · exact prime_oneHundredTwoCV_12218187282907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 13219223366995570511) ^ 6609611683497785255 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 13219223366995570511) ^ 2643844673399114102 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 13219223366995570511) ^ 122181872829070 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (11 : ZMod 13219223366995570511) ^ 1081930 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_26253246322513024547 : Nat.Prime 26253246322513024547 := by
  apply lucas_primality 26253246322513024547 (2 : ZMod 26253246322513024547)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (649927081, 1), (20197070633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (649927081, 1), (20197070633, 1)] : List FactorBlock).map factorBlockValue).prod) = 26253246322513024547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_649927081
      · exact prime_oneHundredTwoCV_20197070633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26253246322513024547) ^ 13126623161256512273 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 26253246322513024547) ^ 40394141266 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 26253246322513024547) ^ 1299854162 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_26438446733991141023 : Nat.Prime 26438446733991141023 := by
  apply lucas_primality 26438446733991141023 (5 : ZMod 26438446733991141023)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13219223366995570511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13219223366995570511, 1)] : List FactorBlock).map factorBlockValue).prod) = 26438446733991141023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13219223366995570511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 26438446733991141023) ^ 13219223366995570511 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 26438446733991141023) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_52990915547505488099 : Nat.Prime 52990915547505488099 := by
  apply lucas_primality 52990915547505488099 (2 : ZMod 52990915547505488099)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (347, 1), (487, 1), (132534287227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (347, 1), (487, 1), (132534287227, 1)] : List FactorBlock).map factorBlockValue).prod) = 52990915547505488099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_347
      · exact prime_oneHundredTwoCV_487
      · exact prime_oneHundredTwoCV_132534287227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52990915547505488099) ^ 26495457773752744049 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52990915547505488099) ^ 7570130792500784014 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52990915547505488099) ^ 4076224272885037546 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52990915547505488099) ^ 152711572183012934 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52990915547505488099) ^ 108810914881941454 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52990915547505488099) ^ 399827974 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_53781335241365175077 : Nat.Prime 53781335241365175077 := by
  apply lucas_primality 53781335241365175077 (2 : ZMod 53781335241365175077)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4159, 1), (3232828518956791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4159, 1), (3232828518956791, 1)] : List FactorBlock).map factorBlockValue).prod) = 53781335241365175077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_4159
      · exact prime_oneHundredTwoCV_3232828518956791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53781335241365175077) ^ 26890667620682587538 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 53781335241365175077) ^ 12931314075827164 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 53781335241365175077) ^ 16636 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_72696040373371644391 : Nat.Prime 72696040373371644391 := by
  apply lucas_primality 72696040373371644391 (15 : ZMod 72696040373371644391)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (2857381, 1), (6376314181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (2857381, 1), (6376314181, 1)] : List FactorBlock).map factorBlockValue).prod) = 72696040373371644391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_2857381
      · exact prime_oneHundredTwoCV_6376314181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 72696040373371644391) ^ 36348020186685822195 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 72696040373371644391) ^ 24232013457790548130 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 72696040373371644391) ^ 14539208074674328878 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 72696040373371644391) ^ 10385148624767377770 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 72696040373371644391) ^ 3826107388072191810 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 72696040373371644391) ^ 25441493582190 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 72696040373371644391) ^ 11400950190 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_87883847601009236017 : Nat.Prime 87883847601009236017 := by
  apply lucas_primality 87883847601009236017 (5 : ZMod 87883847601009236017)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (191, 1), (330549465912203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (191, 1), (330549465912203, 1)] : List FactorBlock).map factorBlockValue).prod) = 87883847601009236017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_191
      · exact prime_oneHundredTwoCV_330549465912203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 87883847601009236017) ^ 43941923800504618008 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 87883847601009236017) ^ 29294615867003078672 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 87883847601009236017) ^ 3030477503483077104 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 87883847601009236017) ^ 460124856549786576 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 87883847601009236017) ^ 265872 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_139033894650548762957 : Nat.Prime 139033894650548762957 := by
  apply lucas_primality 139033894650548762957 (2 : ZMod 139033894650548762957)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (16103, 1), (2935157, 1), (8081299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (16103, 1), (2935157, 1), (8081299, 1)] : List FactorBlock).map factorBlockValue).prod) = 139033894650548762957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_16103
      · exact prime_oneHundredTwoCV_2935157
      · exact prime_oneHundredTwoCV_8081299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139033894650548762957) ^ 69516947325274381478 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139033894650548762957) ^ 19861984950078394708 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139033894650548762957) ^ 10694914973119135612 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139033894650548762957) ^ 8634036803735252 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139033894650548762957) ^ 47368469438108 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139033894650548762957) ^ 17204399274244 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_161972944324452468007 : Nat.Prime 161972944324452468007 := by
  apply lucas_primality 161972944324452468007 (3 : ZMod 161972944324452468007)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (743, 1), (36333096528589607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (743, 1), (36333096528589607, 1)] : List FactorBlock).map factorBlockValue).prod) = 161972944324452468007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_743
      · exact prime_oneHundredTwoCV_36333096528589607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 161972944324452468007) ^ 80986472162226234003 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 161972944324452468007) ^ 53990981441484156002 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 161972944324452468007) ^ 217998579171537642 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 161972944324452468007) ^ 4458 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_241011563302409355101 : Nat.Prime 241011563302409355101 := by
  apply lucas_primality 241011563302409355101 (2 : ZMod 241011563302409355101)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (349, 1), (631, 1), (15277, 1), (716382577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (349, 1), (631, 1), (15277, 1), (716382577, 1)] : List FactorBlock).map factorBlockValue).prod) = 241011563302409355101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_349
      · exact prime_oneHundredTwoCV_631
      · exact prime_oneHundredTwoCV_15277
      · exact prime_oneHundredTwoCV_716382577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 241011563302409355101) ^ 120505781651204677550 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241011563302409355101) ^ 48202312660481871020 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241011563302409355101) ^ 690577545279109900 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241011563302409355101) ^ 381951764346132100 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241011563302409355101) ^ 15776105472436300 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241011563302409355101) ^ 336428566300 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_304226153104171181309 : Nat.Prime 304226153104171181309 := by
  apply lucas_primality 304226153104171181309 (2 : ZMod 304226153104171181309)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (28619, 1), (2657554012231133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (28619, 1), (2657554012231133, 1)] : List FactorBlock).map factorBlockValue).prod) = 304226153104171181309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_28619
      · exact prime_oneHundredTwoCV_2657554012231133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 304226153104171181309) ^ 152113076552085590654 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 304226153104171181309) ^ 10630216048924532 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 304226153104171181309) ^ 114476 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_423927324380043904793 : Nat.Prime 423927324380043904793 := by
  apply lucas_primality 423927324380043904793 (3 : ZMod 423927324380043904793)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (52990915547505488099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (52990915547505488099, 1)] : List FactorBlock).map factorBlockValue).prod) = 423927324380043904793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_52990915547505488099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 423927324380043904793) ^ 211963662190021952396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 423927324380043904793) ^ 8 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_441306033115599513151 : Nat.Prime 441306033115599513151 := by
  apply lucas_primality 441306033115599513151 (15 : ZMod 441306033115599513151)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (3491, 1), (68669, 1), (12272641099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (3491, 1), (68669, 1), (12272641099, 1)] : List FactorBlock).map factorBlockValue).prod) = 441306033115599513151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_3491
      · exact prime_oneHundredTwoCV_68669
      · exact prime_oneHundredTwoCV_12272641099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 441306033115599513151) ^ 220653016557799756575 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 441306033115599513151) ^ 147102011038533171050 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 441306033115599513151) ^ 88261206623119902630 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 441306033115599513151) ^ 126412498744084650 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 441306033115599513151) ^ 6426568511491350 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (15 : ZMod 441306033115599513151) ^ 35958521850 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_449168195151489808409 : Nat.Prime 449168195151489808409 := by
  apply lucas_primality 449168195151489808409 (3 : ZMod 449168195151489808409)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (101, 1), (4261, 1), (673793, 1), (3174167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (101, 1), (4261, 1), (673793, 1), (3174167, 1)] : List FactorBlock).map factorBlockValue).prod) = 449168195151489808409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_61
      · exact prime_oneHundredTwoCV_101
      · exact prime_oneHundredTwoCV_4261
      · exact prime_oneHundredTwoCV_673793
      · exact prime_oneHundredTwoCV_3174167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 449168195151489808409) ^ 224584097575744904204 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 449168195151489808409) ^ 7363413035270324728 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 449168195151489808409) ^ 4447209852985047608 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 449168195151489808409) ^ 105413798439683128 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 449168195151489808409) ^ 666626389932056 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 449168195151489808409) ^ 141507423885224 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_527303085606055416103 : Nat.Prime 527303085606055416103 := by
  apply lucas_primality 527303085606055416103 (5 : ZMod 527303085606055416103)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (87883847601009236017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (87883847601009236017, 1)] : List FactorBlock).map factorBlockValue).prod) = 527303085606055416103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_87883847601009236017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 527303085606055416103) ^ 263651542803027708051 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 527303085606055416103) ^ 175767695202018472034 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 527303085606055416103) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_640211286050277169477 : Nat.Prime 640211286050277169477 := by
  apply lucas_primality 640211286050277169477 (2 : ZMod 640211286050277169477)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (37, 1), (6793, 1), (7319488677107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (37, 1), (6793, 1), (7319488677107, 1)] : List FactorBlock).map factorBlockValue).prod) = 640211286050277169477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_6793
      · exact prime_oneHundredTwoCV_7319488677107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640211286050277169477) ^ 320105643025138584738 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 640211286050277169477) ^ 213403762016759056492 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 640211286050277169477) ^ 22076251243113005844 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 640211286050277169477) ^ 17303007731088572148 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 640211286050277169477) ^ 94245736206429732 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 640211286050277169477) ^ 87466668 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_655868662880733981149 : Nat.Prime 655868662880733981149 := by
  apply lucas_primality 655868662880733981149 (2 : ZMod 655868662880733981149)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (439, 1), (1103, 1), (996263, 1), (339893497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (439, 1), (1103, 1), (996263, 1), (339893497, 1)] : List FactorBlock).map factorBlockValue).prod) = 655868662880733981149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_439
      · exact prime_oneHundredTwoCV_1103
      · exact prime_oneHundredTwoCV_996263
      · exact prime_oneHundredTwoCV_339893497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 655868662880733981149) ^ 327934331440366990574 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 655868662880733981149) ^ 1494006065787548932 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 655868662880733981149) ^ 594622541143004516 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 655868662880733981149) ^ 658328837747396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 655868662880733981149) ^ 1929629924284 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_847854648760087809587 : Nat.Prime 847854648760087809587 := by
  apply lucas_primality 847854648760087809587 (2 : ZMod 847854648760087809587)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (423927324380043904793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (423927324380043904793, 1)] : List FactorBlock).map factorBlockValue).prod) = 847854648760087809587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_423927324380043904793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 847854648760087809587) ^ 423927324380043904793 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 847854648760087809587) ^ 2 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_951938330765685269581 : Nat.Prime 951938330765685269581 := by
  apply lucas_primality 951938330765685269581 (14 : ZMod 951938330765685269581)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (400773641, 1), (1885120513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (400773641, 1), (1885120513, 1)] : List FactorBlock).map factorBlockValue).prod) = 951938330765685269581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_400773641
      · exact prime_oneHundredTwoCV_1885120513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 951938330765685269581) ^ 475969165382842634790 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 951938330765685269581) ^ 317312776921895089860 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 951938330765685269581) ^ 190387666153137053916 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 951938330765685269581) ^ 135991190109383609940 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 951938330765685269581) ^ 2375251846380 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (14 : ZMod 951938330765685269581) ^ 504974787660 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1203547527708862339403 : Nat.Prime 1203547527708862339403 := by
  apply lucas_primality 1203547527708862339403 (2 : ZMod 1203547527708862339403)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 2), (389, 1), (1109, 1), (145562871347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 2), (389, 1), (1109, 1), (145562871347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1203547527708862339403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_389
      · exact prime_oneHundredTwoCV_1109
      · exact prime_oneHundredTwoCV_145562871347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1203547527708862339403) ^ 601773763854431169701 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203547527708862339403) ^ 171935361101266048486 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203547527708862339403) ^ 32528311559698982146 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203547527708862339403) ^ 3093952513390391618 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203547527708862339403) ^ 1085254758980038178 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203547527708862339403) ^ 8268231566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2020803087705013130917 : Nat.Prime 2020803087705013130917 := by
  apply lucas_primality 2020803087705013130917 (2 : ZMod 2020803087705013130917)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (135277, 1), (1244855055247759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (135277, 1), (1244855055247759, 1)] : List FactorBlock).map factorBlockValue).prod) = 2020803087705013130917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_135277
      · exact prime_oneHundredTwoCV_1244855055247759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2020803087705013130917) ^ 1010401543852506565458 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020803087705013130917) ^ 673601029235004376972 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020803087705013130917) ^ 14938260662973108 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020803087705013130917) ^ 1623324 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2259056049321141487189 : Nat.Prime 2259056049321141487189 := by
  apply lucas_primality 2259056049321141487189 (2 : ZMod 2259056049321141487189)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (866513, 1), (72418482960541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (866513, 1), (72418482960541, 1)] : List FactorBlock).map factorBlockValue).prod) = 2259056049321141487189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_866513
      · exact prime_oneHundredTwoCV_72418482960541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2259056049321141487189) ^ 1129528024660570743594 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2259056049321141487189) ^ 753018683107047162396 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2259056049321141487189) ^ 2607065386579476 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2259056049321141487189) ^ 31194468 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2271616630545858501629 : Nat.Prime 2271616630545858501629 := by
  apply lucas_primality 2271616630545858501629 (2 : ZMod 2271616630545858501629)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (991, 1), (573061713053950177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (991, 1), (573061713053950177, 1)] : List FactorBlock).map factorBlockValue).prod) = 2271616630545858501629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_991
      · exact prime_oneHundredTwoCV_573061713053950177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2271616630545858501629) ^ 1135808315272929250814 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2271616630545858501629) ^ 2292246852215800708 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2271616630545858501629) ^ 3964 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_2647836198693597078907 : Nat.Prime 2647836198693597078907 := by
  apply lucas_primality 2647836198693597078907 (3 : ZMod 2647836198693597078907)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (441306033115599513151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (441306033115599513151, 1)] : List FactorBlock).map factorBlockValue).prod) = 2647836198693597078907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_441306033115599513151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2647836198693597078907) ^ 1323918099346798539453 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2647836198693597078907) ^ 882612066231199026302 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2647836198693597078907) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_3004772259021847233389 : Nat.Prime 3004772259021847233389 := by
  apply lucas_primality 3004772259021847233389 (2 : ZMod 3004772259021847233389)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (10909, 1), (9837134014581169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (10909, 1), (9837134014581169, 1)] : List FactorBlock).map factorBlockValue).prod) = 3004772259021847233389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_10909
      · exact prime_oneHundredTwoCV_9837134014581169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3004772259021847233389) ^ 1502386129510923616694 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3004772259021847233389) ^ 429253179860263890484 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3004772259021847233389) ^ 275439752408272732 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3004772259021847233389) ^ 305452 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6331478616472686952543 : Nat.Prime 6331478616472686952543 := by
  apply lucas_primality 6331478616472686952543 (3 : ZMod 6331478616472686952543)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (1163, 1), (6599, 1), (439290400897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (1163, 1), (6599, 1), (439290400897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6331478616472686952543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_313
      · exact prime_oneHundredTwoCV_1163
      · exact prime_oneHundredTwoCV_6599
      · exact prime_oneHundredTwoCV_439290400897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6331478616472686952543) ^ 3165739308236343476271 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6331478616472686952543) ^ 2110492872157562317514 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6331478616472686952543) ^ 20228366186813696334 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6331478616472686952543) ^ 5444091673665251034 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6331478616472686952543) ^ 959460314664750258 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6331478616472686952543) ^ 14412968286 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_7644297387760290352699 : Nat.Prime 7644297387760290352699 := by
  apply lucas_primality 7644297387760290352699 (3 : ZMod 7644297387760290352699)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227, 1), (563, 1), (5743, 1), (1735854243481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227, 1), (563, 1), (5743, 1), (1735854243481, 1)] : List FactorBlock).map factorBlockValue).prod) = 7644297387760290352699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_227
      · exact prime_oneHundredTwoCV_563
      · exact prime_oneHundredTwoCV_5743
      · exact prime_oneHundredTwoCV_1735854243481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7644297387760290352699) ^ 3822148693880145176349 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7644297387760290352699) ^ 2548099129253430117566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7644297387760290352699) ^ 33675318888811851774 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7644297387760290352699) ^ 13577792873464103646 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7644297387760290352699) ^ 1331063449026691686 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7644297387760290352699) ^ 4403766858 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_8932225265081811220207 : Nat.Prime 8932225265081811220207 := by
  apply lucas_primality 8932225265081811220207 (5 : ZMod 8932225265081811220207)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (29, 1), (199, 1), (4866599, 1), (329234929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (29, 1), (199, 1), (4866599, 1), (329234929, 1)] : List FactorBlock).map factorBlockValue).prod) = 8932225265081811220207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_199
      · exact prime_oneHundredTwoCV_4866599
      · exact prime_oneHundredTwoCV_329234929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8932225265081811220207) ^ 4466112632540905610103 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 2977408421693937073402 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 1276032180725973031458 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 388357620220948313922 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 308007767761441766214 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 44885554095888498594 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 1835414272900194 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8932225265081811220207) ^ 27130247972814 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_12633889657307292504547 : Nat.Prime 12633889657307292504547 := by
  apply lucas_primality 12633889657307292504547 (2 : ZMod 12633889657307292504547)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (161972944324452468007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (161972944324452468007, 1)] : List FactorBlock).map factorBlockValue).prod) = 12633889657307292504547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_161972944324452468007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12633889657307292504547) ^ 6316944828653646252273 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12633889657307292504547) ^ 4211296552435764168182 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12633889657307292504547) ^ 971837665946714808042 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12633889657307292504547) ^ 78 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_13642238514739428767869 : Nat.Prime 13642238514739428767869 := by
  apply lucas_primality 13642238514739428767869 (2 : ZMod 13642238514739428767869)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (26438446733991141023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (26438446733991141023, 1)] : List FactorBlock).map factorBlockValue).prod) = 13642238514739428767869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_43
      · exact prime_oneHundredTwoCV_26438446733991141023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13642238514739428767869) ^ 6821119257369714383934 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13642238514739428767869) ^ 4547412838246476255956 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13642238514739428767869) ^ 317261360807893692276 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13642238514739428767869) ^ 516 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_20281915973018023809971 : Nat.Prime 20281915973018023809971 := by
  apply lucas_primality 20281915973018023809971 (2 : ZMod 20281915973018023809971)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (139, 1), (1993, 1), (10828241, 1), (676128071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (139, 1), (1993, 1), (10828241, 1), (676128071, 1)] : List FactorBlock).map factorBlockValue).prod) = 20281915973018023809971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_139
      · exact prime_oneHundredTwoCV_1993
      · exact prime_oneHundredTwoCV_10828241
      · exact prime_oneHundredTwoCV_676128071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20281915973018023809971) ^ 10140957986509011904985 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20281915973018023809971) ^ 4056383194603604761994 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20281915973018023809971) ^ 145913064554086502230 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20281915973018023809971) ^ 10176576002517824290 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20281915973018023809971) ^ 1873057311249170 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20281915973018023809971) ^ 29997151195070 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_28418182592923236827687 : Nat.Prime 28418182592923236827687 := by
  apply lucas_primality 28418182592923236827687 (5 : ZMod 28418182592923236827687)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (191, 1), (5992421, 1), (61155367771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (191, 1), (5992421, 1), (61155367771, 1)] : List FactorBlock).map factorBlockValue).prod) = 28418182592923236827687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_29
      · exact prime_oneHundredTwoCV_191
      · exact prime_oneHundredTwoCV_5992421
      · exact prime_oneHundredTwoCV_61155367771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28418182592923236827687) ^ 14209091296461618413843 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28418182592923236827687) ^ 4059740370417605261098 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28418182592923236827687) ^ 979937330790456442334 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28418182592923236827687) ^ 148786296298027417946 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28418182592923236827687) ^ 4742354149169966 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28418182592923236827687) ^ 464688278866 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_33311986193162227669513 : Nat.Prime 33311986193162227669513 := by
  apply lucas_primality 33311986193162227669513 (5 : ZMod 33311986193162227669513)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (977, 1), (2102783, 1), (675616527493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (977, 1), (2102783, 1), (675616527493, 1)] : List FactorBlock).map factorBlockValue).prod) = 33311986193162227669513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_977
      · exact prime_oneHundredTwoCV_2102783
      · exact prime_oneHundredTwoCV_675616527493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33311986193162227669513) ^ 16655993096581113834756 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 33311986193162227669513) ^ 11103995397720742556504 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 33311986193162227669513) ^ 34096198764751512456 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 33311986193162227669513) ^ 15841856336655864 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 33311986193162227669513) ^ 49306055784 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_49641604412615108400769 : Nat.Prime 49641604412615108400769 := by
  apply lucas_primality 49641604412615108400769 (7 : ZMod 49641604412615108400769)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (19, 1), (6803947973220272533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (19, 1), (6803947973220272533, 1)] : List FactorBlock).map factorBlockValue).prod) = 49641604412615108400769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_6803947973220272533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 49641604412615108400769) ^ 24820802206307554200384 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 49641604412615108400769) ^ 16547201470871702800256 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 49641604412615108400769) ^ 2612716021716584652672 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 49641604412615108400769) ^ 7296 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_57735365187678916337549 : Nat.Prime 57735365187678916337549 := by
  apply lucas_primality 57735365187678916337549 (2 : ZMod 57735365187678916337549)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (13903, 1), (173087, 1), (461387261759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (13903, 1), (173087, 1), (461387261759, 1)] : List FactorBlock).map factorBlockValue).prod) = 57735365187678916337549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_13903
      · exact prime_oneHundredTwoCV_173087
      · exact prime_oneHundredTwoCV_461387261759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57735365187678916337549) ^ 28867682593839458168774 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57735365187678916337549) ^ 4441181937513762795196 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57735365187678916337549) ^ 4152727122756161716 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57735365187678916337549) ^ 333562689212239604 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57735365187678916337549) ^ 125134285172 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_72691732177467472052129 : Nat.Prime 72691732177467472052129 := by
  apply lucas_primality 72691732177467472052129 (3 : ZMod 72691732177467472052129)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2271616630545858501629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2271616630545858501629, 1)] : List FactorBlock).map factorBlockValue).prod) = 72691732177467472052129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_2271616630545858501629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 72691732177467472052129) ^ 36345866088733736026064 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 72691732177467472052129) ^ 32 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_121441922848038397057547 : Nat.Prime 121441922848038397057547 := by
  apply lucas_primality 121441922848038397057547 (2 : ZMod 121441922848038397057547)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (11279, 1), (55871, 1), (5668037001541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (11279, 1), (55871, 1), (5668037001541, 1)] : List FactorBlock).map factorBlockValue).prod) = 121441922848038397057547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_11279
      · exact prime_oneHundredTwoCV_55871
      · exact prime_oneHundredTwoCV_5668037001541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121441922848038397057547) ^ 60720961424019198528773 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 121441922848038397057547) ^ 7143642520472846885738 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 121441922848038397057547) ^ 10767082440645305174 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 121441922848038397057547) ^ 2173612837572951926 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 121441922848038397057547) ^ 21425746306 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_163405839919033542758479 : Nat.Prime 163405839919033542758479 := by
  apply lucas_primality 163405839919033542758479 (3 : ZMod 163405839919033542758479)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (241011563302409355101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (241011563302409355101, 1)] : List FactorBlock).map factorBlockValue).prod) = 163405839919033542758479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_113
      · exact prime_oneHundredTwoCV_241011563302409355101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 163405839919033542758479) ^ 81702919959516771379239 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 163405839919033542758479) ^ 54468613306344514252826 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 163405839919033542758479) ^ 1446069379814456130606 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 163405839919033542758479) ^ 678 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_215324934296987710026121 : Nat.Prime 215324934296987710026121 := by
  apply lucas_primality 215324934296987710026121 (37 : ZMod 215324934296987710026121)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (3833, 1), (50174297, 1), (491065429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (3833, 1), (50174297, 1), (491065429, 1)] : List FactorBlock).map factorBlockValue).prod) = 215324934296987710026121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_3833
      · exact prime_oneHundredTwoCV_50174297
      · exact prime_oneHundredTwoCV_491065429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 215324934296987710026121) ^ 107662467148493855013060 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (37 : ZMod 215324934296987710026121) ^ 71774978098995903342040 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (37 : ZMod 215324934296987710026121) ^ 43064986859397542005224 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (37 : ZMod 215324934296987710026121) ^ 11332891278788826843480 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (37 : ZMod 215324934296987710026121) ^ 56176606912858781640 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (37 : ZMod 215324934296987710026121) ^ 4291538639733960 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (37 : ZMod 215324934296987710026121) ^ 438485223314280 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_273386251203775743674159 : Nat.Prime 273386251203775743674159 := by
  apply lucas_primality 273386251203775743674159 (7 : ZMod 273386251203775743674159)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5711, 1), (10826177, 1), (315835796351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5711, 1), (10826177, 1), (315835796351, 1)] : List FactorBlock).map factorBlockValue).prod) = 273386251203775743674159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_5711
      · exact prime_oneHundredTwoCV_10826177
      · exact prime_oneHundredTwoCV_315835796351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 273386251203775743674159) ^ 136693125601887871837079 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 273386251203775743674159) ^ 39055178743396534810594 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 273386251203775743674159) ^ 47870119279246321778 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 273386251203775743674159) ^ 25252335261447854 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 273386251203775743674159) ^ 865596155858 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_318549943281535406487583 : Nat.Prime 318549943281535406487583 := by
  apply lucas_primality 318549943281535406487583 (3 : ZMod 318549943281535406487583)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (994453, 1), (498951395668307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (994453, 1), (498951395668307, 1)] : List FactorBlock).map factorBlockValue).prod) = 318549943281535406487583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_107
      · exact prime_oneHundredTwoCV_994453
      · exact prime_oneHundredTwoCV_498951395668307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 318549943281535406487583) ^ 159274971640767703243791 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 318549943281535406487583) ^ 106183314427178468829194 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 318549943281535406487583) ^ 2977102273659209406426 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 318549943281535406487583) ^ 320326796019053094 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 318549943281535406487583) ^ 638438826 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_565707125231566916794463 : Nat.Prime 565707125231566916794463 := by
  apply lucas_primality 565707125231566916794463 (5 : ZMod 565707125231566916794463)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (1087, 1), (28439897, 1), (35326802131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (1087, 1), (28439897, 1), (35326802131, 1)] : List FactorBlock).map factorBlockValue).prod) = 565707125231566916794463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_1087
      · exact prime_oneHundredTwoCV_28439897
      · exact prime_oneHundredTwoCV_35326802131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 565707125231566916794463) ^ 282853562615783458397231 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 565707125231566916794463) ^ 80815303604509559542066 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 565707125231566916794463) ^ 15289381763015322075526 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 565707125231566916794463) ^ 520429738023520622626 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 565707125231566916794463) ^ 19891321168693646 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 565707125231566916794463) ^ 16013539044202 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_1729774398314392714425287 : Nat.Prime 1729774398314392714425287 := by
  apply lucas_primality 1729774398314392714425287 (5 : ZMod 1729774398314392714425287)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (305587259, 1), (76493142362821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (305587259, 1), (76493142362821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1729774398314392714425287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_37
      · exact prime_oneHundredTwoCV_305587259
      · exact prime_oneHundredTwoCV_76493142362821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1729774398314392714425287) ^ 864887199157196357212643 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729774398314392714425287) ^ 46750659413902505795278 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729774398314392714425287) ^ 5660492534848754 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729774398314392714425287) ^ 22613457166 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_4287230595082760526385057 : Nat.Prime 4287230595082760526385057 := by
  apply lucas_primality 4287230595082760526385057 (5 : ZMod 4287230595082760526385057)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (39713719, 1), (374838159680723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (39713719, 1), (374838159680723, 1)] : List FactorBlock).map factorBlockValue).prod) = 4287230595082760526385057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_39713719
      · exact prime_oneHundredTwoCV_374838159680723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4287230595082760526385057) ^ 2143615297541380263192528 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4287230595082760526385057) ^ 1429076865027586842128352 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4287230595082760526385057) ^ 107953389988048224 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4287230595082760526385057) ^ 11437551072 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_5890256541712884681588379 : Nat.Prime 5890256541712884681588379 := by
  apply lucas_primality 5890256541712884681588379 (2 : ZMod 5890256541712884681588379)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (211, 1), (37511, 1), (706523, 1), (13504303997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (211, 1), (37511, 1), (706523, 1), (13504303997, 1)] : List FactorBlock).map factorBlockValue).prod) = 5890256541712884681588379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_211
      · exact prime_oneHundredTwoCV_37511
      · exact prime_oneHundredTwoCV_706523
      · exact prime_oneHundredTwoCV_13504303997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5890256541712884681588379) ^ 2945128270856442340794189 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5890256541712884681588379) ^ 1963418847237628227196126 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5890256541712884681588379) ^ 453096657054837283199106 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5890256541712884681588379) ^ 27915907780629785220798 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5890256541712884681588379) ^ 157027446394734469398 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5890256541712884681588379) ^ 8336963611535483886 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5890256541712884681588379) ^ 436176240035874 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_7765049721731351454356657 : Nat.Prime 7765049721731351454356657 := by
  apply lucas_primality 7765049721731351454356657 (3 : ZMod 7765049721731351454356657)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5426387, 1), (89436232175885993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5426387, 1), (89436232175885993, 1)] : List FactorBlock).map factorBlockValue).prod) = 7765049721731351454356657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5426387
      · exact prime_oneHundredTwoCV_89436232175885993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7765049721731351454356657) ^ 3882524860865675727178328 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7765049721731351454356657) ^ 1430979714814175888 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7765049721731351454356657) ^ 86822192 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_19563793344985056470823959 : Nat.Prime 19563793344985056470823959 := by
  apply lucas_primality 19563793344985056470823959 (17 : ZMod 19563793344985056470823959)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2767, 1), (270853787, 1), (13052058141151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2767, 1), (270853787, 1), (13052058141151, 1)] : List FactorBlock).map factorBlockValue).prod) = 19563793344985056470823959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_2767
      · exact prime_oneHundredTwoCV_270853787
      · exact prime_oneHundredTwoCV_13052058141151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 19563793344985056470823959) ^ 9781896672492528235411979 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19563793344985056470823959) ^ 7070398751349857777674 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19563793344985056470823959) ^ 72230089753129634 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19563793344985056470823959) ^ 1498904857258 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_34984398659265415748813137 : Nat.Prime 34984398659265415748813137 := by
  apply lucas_primality 34984398659265415748813137 (5 : ZMod 34984398659265415748813137)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (383, 1), (24922517, 1), (1139640037511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (383, 1), (24922517, 1), (1139640037511, 1)] : List FactorBlock).map factorBlockValue).prod) = 34984398659265415748813137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_67
      · exact prime_oneHundredTwoCV_383
      · exact prime_oneHundredTwoCV_24922517
      · exact prime_oneHundredTwoCV_1139640037511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34984398659265415748813137) ^ 17492199329632707874406568 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34984398659265415748813137) ^ 11661466219755138582937712 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34984398659265415748813137) ^ 522155203869633070877808 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34984398659265415748813137) ^ 91343077439335289161392 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34984398659265415748813137) ^ 1403726544123349008 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34984398659265415748813137) ^ 30697762019376 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_94879010368597866314837831 : Nat.Prime 94879010368597866314837831 := by
  apply lucas_primality 94879010368597866314837831 (7 : ZMod 94879010368597866314837831)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (2399, 1), (304226153104171181309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (2399, 1), (304226153104171181309, 1)] : List FactorBlock).map factorBlockValue).prod) = 94879010368597866314837831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_2399
      · exact prime_oneHundredTwoCV_304226153104171181309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 94879010368597866314837831) ^ 47439505184298933157418915 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 94879010368597866314837831) ^ 18975802073719573262967566 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 94879010368597866314837831) ^ 7298385412969066639602910 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 94879010368597866314837831) ^ 39549399903542253570170 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 94879010368597866314837831) ^ 311870 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_118110893416736423198980297 : Nat.Prime 118110893416736423198980297 := by
  apply lucas_primality 118110893416736423198980297 (10 : ZMod 118110893416736423198980297)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (1037121121, 1), (19211102133317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (1037121121, 1), (19211102133317, 1)] : List FactorBlock).map factorBlockValue).prod) = 118110893416736423198980297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_19
      · exact prime_oneHundredTwoCV_1037121121
      · exact prime_oneHundredTwoCV_19211102133317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 118110893416736423198980297) ^ 59055446708368211599490148 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 118110893416736423198980297) ^ 39370297805578807732993432 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 118110893416736423198980297) ^ 9085453339748955630690792 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 118110893416736423198980297) ^ 6216362811407180168367384 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 118110893416736423198980297) ^ 113883413446303176 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (10 : ZMod 118110893416736423198980297) ^ 6148054005288 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_165647283212208637480987477 : Nat.Prime 165647283212208637480987477 := by
  apply lucas_primality 165647283212208637480987477 (7 : ZMod 165647283212208637480987477)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 2), (180679, 1), (45783767, 1), (3291363973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 2), (180679, 1), (45783767, 1), (3291363973, 1)] : List FactorBlock).map factorBlockValue).prod) = 165647283212208637480987477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_180679
      · exact prime_oneHundredTwoCV_45783767
      · exact prime_oneHundredTwoCV_3291363973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 165647283212208637480987477) ^ 82823641606104318740493738 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 165647283212208637480987477) ^ 55215761070736212493662492 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 165647283212208637480987477) ^ 12742098708631433652383652 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 165647283212208637480987477) ^ 916804294977327954444 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 165647283212208637480987477) ^ 3618035257173326028 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 165647283212208637480987477) ^ 50327853306732612 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_177340032615423364832586593 : Nat.Prime 177340032615423364832586593 := by
  apply lucas_primality 177340032615423364832586593 (3 : ZMod 177340032615423364832586593)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (6100111, 1), (908487733949756021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (6100111, 1), (908487733949756021, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364832586593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_6100111
      · exact prime_oneHundredTwoCV_908487733949756021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 177340032615423364832586593) ^ 88670016307711682416293296 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 177340032615423364832586593) ^ 29071607486392192672 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 177340032615423364832586593) ^ 195203552 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_658968427204851847465349089 : Nat.Prime 658968427204851847465349089 := by
  apply lucas_primality 658968427204851847465349089 (7 : ZMod 658968427204851847465349089)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 2), (17, 1), (1071778067, 1), (3113538332287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 2), (17, 1), (1071778067, 1), (3113538332287, 1)] : List FactorBlock).map factorBlockValue).prod) = 658968427204851847465349089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_1071778067
      · exact prime_oneHundredTwoCV_3113538332287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 658968427204851847465349089) ^ 329484213602425923732674544 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 658968427204851847465349089) ^ 219656142401617282488449696 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 658968427204851847465349089) ^ 59906220654986531587759008 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 658968427204851847465349089) ^ 38762848659108932203844064 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 658968427204851847465349089) ^ 614836641553378464 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (7 : ZMod 658968427204851847465349089) ^ 211646158446624 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_666249846289988331967728637 : Nat.Prime 666249846289988331967728637 := by
  apply lucas_primality 666249846289988331967728637 (2 : ZMod 666249846289988331967728637)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (3511, 1), (2259056049321141487189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (3511, 1), (2259056049321141487189, 1)] : List FactorBlock).map factorBlockValue).prod) = 666249846289988331967728637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_3511
      · exact prime_oneHundredTwoCV_2259056049321141487189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 666249846289988331967728637) ^ 333124923144994165983864318 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 666249846289988331967728637) ^ 222083282096662777322576212 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 666249846289988331967728637) ^ 95178549469998333138246948 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 666249846289988331967728637) ^ 189760708142975884923876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 666249846289988331967728637) ^ 294924 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_763235583408151190418727109 : Nat.Prime 763235583408151190418727109 := by
  apply lucas_primality 763235583408151190418727109 (2 : ZMod 763235583408151190418727109)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (34867981, 1), (466787903, 1), (11723363339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (34867981, 1), (466787903, 1), (11723363339, 1)] : List FactorBlock).map factorBlockValue).prod) = 763235583408151190418727109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_34867981
      · exact prime_oneHundredTwoCV_466787903
      · exact prime_oneHundredTwoCV_11723363339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 763235583408151190418727109) ^ 381617791704075595209363554 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 763235583408151190418727109) ^ 21889296756475552468 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 763235583408151190418727109) ^ 1635080040641394236 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 763235583408151190418727109) ^ 65103806931335372 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_913569864988544606713324873 : Nat.Prime 913569864988544606713324873 := by
  apply lucas_primality 913569864988544606713324873 (5 : ZMod 913569864988544606713324873)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (17, 1), (61, 1), (1071778067, 1), (3113538332287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (17, 1), (61, 1), (1071778067, 1), (3113538332287, 1)] : List FactorBlock).map factorBlockValue).prod) = 913569864988544606713324873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_11
      · exact prime_oneHundredTwoCV_17
      · exact prime_oneHundredTwoCV_61
      · exact prime_oneHundredTwoCV_1071778067
      · exact prime_oneHundredTwoCV_3113538332287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 913569864988544606713324873) ^ 456784932494272303356662436 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 913569864988544606713324873) ^ 304523288329514868904441624 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 913569864988544606713324873) ^ 83051805908049509701211352 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 913569864988544606713324873) ^ 53739403822855565100783816 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 913569864988544606713324873) ^ 14976555163746632896939752 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 913569864988544606713324873) ^ 852387162153547416 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 913569864988544606713324873) ^ 293418537846456 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_4158318006154754761591685629 : Nat.Prime 4158318006154754761591685629 := by
  apply lucas_primality 4158318006154754761591685629 (2 : ZMod 4158318006154754761591685629)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (8467, 1), (13642238514739428767869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (8467, 1), (13642238514739428767869, 1)] : List FactorBlock).map factorBlockValue).prod) = 4158318006154754761591685629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_8467
      · exact prime_oneHundredTwoCV_13642238514739428767869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4158318006154754761591685629) ^ 2079159003077377380795842814 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4158318006154754761591685629) ^ 1386106002051584920530561876 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4158318006154754761591685629) ^ 491120586530619435643284 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4158318006154754761591685629) ^ 304812 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_5481419189931267640279949239 : Nat.Prime 5481419189931267640279949239 := by
  apply lucas_primality 5481419189931267640279949239 (3 : ZMod 5481419189931267640279949239)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (913569864988544606713324873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (913569864988544606713324873, 1)] : List FactorBlock).map factorBlockValue).prod) = 5481419189931267640279949239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_913569864988544606713324873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5481419189931267640279949239) ^ 2740709594965633820139974619 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5481419189931267640279949239) ^ 1827139729977089213426649746 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5481419189931267640279949239) ^ 6 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_6699512343249327115897715737 : Nat.Prime 6699512343249327115897715737 := by
  apply lucas_primality 6699512343249327115897715737 (5 : ZMod 6699512343249327115897715737)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (173, 1), (179, 1), (3004772259021847233389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (173, 1), (179, 1), (3004772259021847233389, 1)] : List FactorBlock).map factorBlockValue).prod) = 6699512343249327115897715737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_173
      · exact prime_oneHundredTwoCV_179
      · exact prime_oneHundredTwoCV_3004772259021847233389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6699512343249327115897715737) ^ 3349756171624663557948857868 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6699512343249327115897715737) ^ 2233170781083109038632571912 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6699512343249327115897715737) ^ 38725504874273567143917432 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6699512343249327115897715737) ^ 37427443258376129139093384 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6699512343249327115897715737) ^ 2229624 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_30147805544621972021539720813 : Nat.Prime 30147805544621972021539720813 := by
  apply lucas_primality 30147805544621972021539720813 (2 : ZMod 30147805544621972021539720813)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (173, 1), (179, 1), (3004772259021847233389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (173, 1), (179, 1), (3004772259021847233389, 1)] : List FactorBlock).map factorBlockValue).prod) = 30147805544621972021539720813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_173
      · exact prime_oneHundredTwoCV_179
      · exact prime_oneHundredTwoCV_3004772259021847233389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30147805544621972021539720813) ^ 15073902772310986010769860406 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30147805544621972021539720813) ^ 10049268514873990673846573604 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30147805544621972021539720813) ^ 174264771934231052147628444 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30147805544621972021539720813) ^ 168423494662692581125920228 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30147805544621972021539720813) ^ 10033308 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_30147805544621972021539720817 : Nat.Prime 30147805544621972021539720817 := by
  apply lucas_primality 30147805544621972021539720817 (3 : ZMod 30147805544621972021539720817)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47, 1), (71, 1), (10499, 1), (53781335241365175077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47, 1), (71, 1), (10499, 1), (53781335241365175077, 1)] : List FactorBlock).map factorBlockValue).prod) = 30147805544621972021539720817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_47
      · exact prime_oneHundredTwoCV_71
      · exact prime_oneHundredTwoCV_10499
      · exact prime_oneHundredTwoCV_53781335241365175077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30147805544621972021539720817) ^ 15073902772310986010769860408 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30147805544621972021539720817) ^ 641442671162169617479568528 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30147805544621972021539720817) ^ 424616979501717915796334096 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30147805544621972021539720817) ^ 2871493051206969427711184 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30147805544621972021539720817) ^ 560562608 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_30147805544621972021539720823 : Nat.Prime 30147805544621972021539720823 := by
  apply lucas_primality 30147805544621972021539720823 (5 : ZMod 30147805544621972021539720823)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1487, 1), (207709, 1), (10738801, 1), (4544683376617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1487, 1), (207709, 1), (10738801, 1), (4544683376617, 1)] : List FactorBlock).map factorBlockValue).prod) = 30147805544621972021539720823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_1487
      · exact prime_oneHundredTwoCV_207709
      · exact prime_oneHundredTwoCV_10738801
      · exact prime_oneHundredTwoCV_4544683376617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30147805544621972021539720823) ^ 15073902772310986010769860411 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30147805544621972021539720823) ^ 20274247171904486900833706 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30147805544621972021539720823) ^ 145144435458367100229358 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30147805544621972021539720823) ^ 2807371655794904107222 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30147805544621972021539720823) ^ 6633642664687366 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_40197074059495962695386294411 : Nat.Prime 40197074059495962695386294411 := by
  apply lucas_primality 40197074059495962695386294411 (3 : ZMod 40197074059495962695386294411)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (23, 1), (1861, 1), (1374105209, 1), (1752409665397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (23, 1), (1861, 1), (1374105209, 1), (1752409665397, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495962695386294411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_5
      · exact prime_oneHundredTwoCV_13
      · exact prime_oneHundredTwoCV_23
      · exact prime_oneHundredTwoCV_1861
      · exact prime_oneHundredTwoCV_1374105209
      · exact prime_oneHundredTwoCV_1752409665397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40197074059495962695386294411) ^ 20098537029747981347693147205 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 13399024686498654231795431470 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 8039414811899192539077258882 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 3092082619961227899645099570 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 1747698872151998378060273670 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 21599717388229963834167810 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 29253272454115238490 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495962695386294411) ^ 22938171851722530 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwoCV_60295611089243944043079441643 : Nat.Prime 60295611089243944043079441643 := by
  apply lucas_primality 60295611089243944043079441643 (2 : ZMod 60295611089243944043079441643)
  · rw [← oneHundredTwoCVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (137, 1), (5641, 1), (32850247, 1), (18849500653133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (137, 1), (5641, 1), (32850247, 1), (18849500653133, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243944043079441643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwoCV_2
      · exact prime_oneHundredTwoCV_3
      · exact prime_oneHundredTwoCV_7
      · exact prime_oneHundredTwoCV_137
      · exact prime_oneHundredTwoCV_5641
      · exact prime_oneHundredTwoCV_32850247
      · exact prime_oneHundredTwoCV_18849500653133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60295611089243944043079441643) ^ 30147805544621972021539720821 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243944043079441643) ^ 20098537029747981347693147214 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243944043079441643) ^ 8613658727034849149011348806 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243944043079441643) ^ 440113949556525139000579866 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243944043079441643) ^ 10688816005893271413415962 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243944043079441643) ^ 1835469032827787993286 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243944043079441643) ^ 3198790896310674 ≠ 1
      rw [← oneHundredTwoCVFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883200 : Nat.totient 120591222178487888086158883200 = 27553874281157785019470110720 := by
  rw [← show ((([(2, 7), (3, 1), (5, 2), (7, 1), (2803, 1), (640211286050277169477, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_2803, prime_oneHundredTwoCV_640211286050277169477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883201 : Nat.totient 120591222178487888086158883201 = 113854812442317439577805396000 := by
  rw [← show ((([(31, 1), (41, 1), (94879010368597866314837831, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_31, prime_oneHundredTwoCV_41, prime_oneHundredTwoCV_94879010368597866314837831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883202 : Nat.totient 120591222178487888086158883202 = 60295611089242901524642498900 := by
  rw [← show ((([(2, 1), (61459738532411, 1), (981058698410291, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_61459738532411, prime_oneHundredTwoCV_981058698410291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883203 : Nat.totient 120591222178487888086158883203 = 73072669703025749274464083200 := by
  rw [← show ((([(3, 2), (11, 1), (5657, 1), (215324934296987710026121, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_5657, prime_oneHundredTwoCV_215324934296987710026121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883204 : Nat.totient 120591222178487888086158883204 = 52728144725896453858062844800 := by
  rw [← show ((([(2, 2), (13, 2), (19, 1), (52519711, 1), (178769354575065181, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_19, prime_oneHundredTwoCV_52519711, prime_oneHundredTwoCV_178769354575065181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883205 : Nat.totient 120591222178487888086158883205 = 94653255075763569333351649920 := by
  rw [← show ((([(5, 1), (73, 1), (191, 1), (1729774398314392714425287, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_73, prime_oneHundredTwoCV_191, prime_oneHundredTwoCV_1729774398314392714425287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883206 : Nat.totient 120591222178487888086158883206 = 37832519303493105647406726656 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (1802597, 1), (655868662880733981149, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_17, prime_oneHundredTwoCV_1802597, prime_oneHundredTwoCV_655868662880733981149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883207 : Nat.totient 120591222178487888086158883207 = 98747304873771190697719819776 := by
  rw [← show ((([(7, 1), (23, 1), (829, 1), (32117, 1), (553627, 1), (50813961734917, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_23, prime_oneHundredTwoCV_829, prime_oneHundredTwoCV_32117, prime_oneHundredTwoCV_553627, prime_oneHundredTwoCV_50813961734917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883208 : Nat.totient 120591222178487888086158883208 = 58676209104734282114525687040 := by
  rw [← show ((([(2, 3), (59, 1), (109, 1), (1583, 1), (3547, 1), (417450606920021971, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_59, prime_oneHundredTwoCV_109, prime_oneHundredTwoCV_1583, prime_oneHundredTwoCV_3547, prime_oneHundredTwoCV_417450606920021971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883209 : Nat.totient 120591222178487888086158883209 = 79194235460322254140712954880 := by
  rw [← show ((([(3, 1), (67, 1), (446931519889, 1), (1342389835013681, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_67, prime_oneHundredTwoCV_446931519889, prime_oneHundredTwoCV_1342389835013681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883210 : Nat.totient 120591222178487888086158883210 = 48205428672508229828646120448 := by
  rw [← show ((([(2, 1), (5, 1), (1553, 1), (7765049721731351454356657, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_1553, prime_oneHundredTwoCV_7765049721731351454356657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883211 : Nat.totient 120591222178487888086158883211 = 120591193760305295162917812072 := by
  rw [← show ((([(4243453, 1), (28418182592923236827687, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_4243453, prime_oneHundredTwoCV_28418182592923236827687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883212 : Nat.totient 120591222178487888086158883212 = 38806384265303425326786883968 := by
  rw [← show ((([(2, 2), (3, 2), (29, 1), (8467, 1), (13642238514739428767869, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_29, prime_oneHundredTwoCV_8467, prime_oneHundredTwoCV_13642238514739428767869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883213 : Nat.totient 120591222178487888086158883213 = 120591222178486578511602188700 := by
  rw [← show ((([(99670031536351, 1), (1209904525158163, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_99670031536351, prime_oneHundredTwoCV_1209904525158163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883214 : Nat.totient 120591222178487888086158883214 = 46893758266626065477265755520 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (523, 1), (11817109933, 1), (126701574339149, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_523, prime_oneHundredTwoCV_11817109933, prime_oneHundredTwoCV_126701574339149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883215 : Nat.totient 120591222178487888086158883215 = 64315051999303995014794784256 := by
  rw [← show ((([(3, 1), (5, 1), (241337, 1), (33311986193162227669513, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_241337, prime_oneHundredTwoCV_33311986193162227669513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883216 : Nat.totient 120591222178487888086158883216 = 60278544667501803315646571136 := by
  rw [← show ((([(2, 4), (3533, 1), (3741110759, 1), (570231901999483, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3533, prime_oneHundredTwoCV_3741110759, prime_oneHundredTwoCV_570231901999483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883217 : Nat.totient 120591222178487888086158883217 = 106326482839328528711507865600 := by
  rw [← show ((([(13, 1), (43, 1), (47, 1), (1231, 1), (46298561, 1), (80534225233919, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_43, prime_oneHundredTwoCV_47, prime_oneHundredTwoCV_1231, prime_oneHundredTwoCV_46298561, prime_oneHundredTwoCV_80534225233919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883218 : Nat.totient 120591222178487888086158883218 = 40196527286993555143898799056 := by
  rw [← show ((([(2, 1), (3, 1), (73517, 1), (273386251203775743674159, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_73517, prime_oneHundredTwoCV_273386251203775743674159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883219 : Nat.totient 120591222178487888086158883219 = 120591222178337791459154924544 := by
  rw [← show ((([(803428232083, 1), (150095823575726593, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_803428232083, prime_oneHundredTwoCV_150095823575726593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883220 : Nat.totient 120591222178487888086158883220 = 48225810520972950994970261760 := by
  rw [← show ((([(2, 2), (5, 1), (5011, 1), (45833, 1), (26253246322513024547, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_5011, prime_oneHundredTwoCV_45833, prime_oneHundredTwoCV_26253246322513024547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883221 : Nat.totient 120591222178487888086158883221 = 68131661157873282159213143040 := by
  rw [← show ((([(3, 3), (7, 1), (163, 1), (193, 1), (20281915973018023809971, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_163, prime_oneHundredTwoCV_193, prime_oneHundredTwoCV_20281915973018023809971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883222 : Nat.totient 120591222178487888086158883222 = 59532375505835792852660714424 := by
  rw [← show ((([(2, 1), (79, 1), (763235583408151190418727109, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_79, prime_oneHundredTwoCV_763235583408151190418727109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883223 : Nat.totient 120591222178487888086158883223 = 106405388837461131629865541632 := by
  rw [← show ((([(17, 1), (19, 2), (149, 1), (269, 1), (13439966713, 1), (36477312343, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_17, prime_oneHundredTwoCV_19, prime_oneHundredTwoCV_149, prime_oneHundredTwoCV_269, prime_oneHundredTwoCV_13439966713, prime_oneHundredTwoCV_36477312343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883224 : Nat.totient 120591222178487888086158883224 = 40123669841673964505357798400 := by
  rw [← show ((([(2, 3), (3, 1), (563, 1), (20021, 1), (19684871, 1), (22645281381097, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_563, prime_oneHundredTwoCV_20021, prime_oneHundredTwoCV_19684871, prime_oneHundredTwoCV_22645281381097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883225 : Nat.totient 120591222178487888086158883225 = 87608430764536990581681408000 := by
  rw [← show ((([(5, 2), (11, 2), (1741, 1), (1997, 1), (9353189, 1), (1225896405133, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_1741, prime_oneHundredTwoCV_1997, prime_oneHundredTwoCV_9353189, prime_oneHundredTwoCV_1225896405133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883226 : Nat.totient 120591222178487888086158883226 = 59307154086674243868766930800 := by
  rw [← show ((([(2, 1), (61, 1), (13597063, 1), (72696040373371644391, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_61, prime_oneHundredTwoCV_13597063, prime_oneHundredTwoCV_72696040373371644391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883227 : Nat.totient 120591222178487888086158883227 = 80391076464448649930898944960 := by
  rw [← show ((([(3, 1), (26183, 1), (67937063, 1), (22597909673617721, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_26183, prime_oneHundredTwoCV_67937063, prime_oneHundredTwoCV_22597909673617721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883228 : Nat.totient 120591222178487888086158883228 = 50706220043760268801062712320 := by
  rw [← show ((([(2, 2), (7, 1), (53, 1), (130769, 1), (237631, 1), (2615013272573203, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_53, prime_oneHundredTwoCV_130769, prime_oneHundredTwoCV_237631, prime_oneHundredTwoCV_2615013272573203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883229 : Nat.totient 120591222178487888086158883229 = 119112194791831719193836661440 := by
  rw [← show ((([(83, 1), (4561, 1), (318549943281535406487583, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_83, prime_oneHundredTwoCV_4561, prime_oneHundredTwoCV_318549943281535406487583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883230 : Nat.totient 120591222178487888086158883230 = 28378127675161672069967585280 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (13, 1), (23, 1), (1861, 1), (1374105209, 1), (1752409665397, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_23, prime_oneHundredTwoCV_1861, prime_oneHundredTwoCV_1374105209, prime_oneHundredTwoCV_1752409665397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883231 : Nat.totient 120591222178487888086158883231 = 120591220974940360377196347352 := by
  rw [← show ((([(100196477, 1), (1203547527708862339403, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_100196477, prime_oneHundredTwoCV_1203547527708862339403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883232 : Nat.totient 120591222178487888086158883232 = 57805258595144348545943212800 := by
  rw [← show ((([(2, 5), (31, 1), (107, 1), (380661763, 1), (2984564659794131, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_31, prime_oneHundredTwoCV_107, prime_oneHundredTwoCV_380661763, prime_oneHundredTwoCV_2984564659794131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883233 : Nat.totient 120591222178487888086158883233 = 80394148118991925390772588820 := by
  rw [← show ((([(3, 1), (40197074059495962695386294411, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_40197074059495962695386294411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883234 : Nat.totient 120591222178487888086158883234 = 59820842476600846942340660544 := by
  rw [← show ((([(2, 1), (127, 1), (2796776959, 1), (169755614485484369, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_127, prime_oneHundredTwoCV_2796776959, prime_oneHundredTwoCV_169755614485484369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883235 : Nat.totient 120591222178487888086158883235 = 80456227283349104694665680512 := by
  rw [← show ((([(5, 1), (7, 1), (37, 1), (63909907, 1), (1457061029471741119, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_37, prime_oneHundredTwoCV_63909907, prime_oneHundredTwoCV_1457061029471741119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883236 : Nat.totient 120591222178487888086158883236 = 36542794599541784268532994880 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (913569864988544606713324873, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_913569864988544606713324873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883237 : Nat.totient 120591222178487888086158883237 = 120473111285071151662959901920 := by
  rw [← show ((([(1021, 1), (118110893416736423198980297, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_1021, prime_oneHundredTwoCV_118110893416736423198980297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883238 : Nat.totient 120591222178487888086158883238 = 59602689396510301279993075200 := by
  rw [← show ((([(2, 1), (89, 1), (4051, 1), (82387, 1), (23223209, 1), (87408271387, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_89, prime_oneHundredTwoCV_4051, prime_oneHundredTwoCV_82387, prime_oneHundredTwoCV_23223209, prime_oneHundredTwoCV_87408271387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883239 : Nat.totient 120591222178487888086158883239 = 80184241727036332896279707712 := by
  rw [← show ((([(3, 2), (383, 1), (34984398659265415748813137, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_383, prime_oneHundredTwoCV_34984398659265415748813137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883240 : Nat.totient 120591222178487888086158883240 = 45399048349548381397142167552 := by
  rw [← show ((([(2, 3), (5, 1), (17, 1), (177340032615423364832586593, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_17, prime_oneHundredTwoCV_177340032615423364832586593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883241 : Nat.totient 120591222178487888086158883241 = 116432904172333133324567197584 := by
  rw [← show ((([(29, 1), (4158318006154754761591685629, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_29, prime_oneHundredTwoCV_4158318006154754761591685629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883242 : Nat.totient 120591222178487888086158883242 = 31758045499399188304060830720 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (19, 1), (41, 1), (367, 1), (110069, 1), (13034663486071679, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_19, prime_oneHundredTwoCV_41, prime_oneHundredTwoCV_367, prime_oneHundredTwoCV_110069, prime_oneHundredTwoCV_13034663486071679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883243 : Nat.totient 120591222178487888086158883243 = 110828094255183859734065184768 := by
  rw [← show ((([(13, 1), (257, 1), (2063, 1), (27089954753, 1), (645850073657, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_257, prime_oneHundredTwoCV_2063, prime_oneHundredTwoCV_27089954753, prime_oneHundredTwoCV_645850073657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883244 : Nat.totient 120591222178487888086158883244 = 60295593224793413879450250864 := by
  rw [← show ((([(2, 2), (3375173, 1), (8932225265081811220207, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3375173, prime_oneHundredTwoCV_8932225265081811220207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883245 : Nat.totient 120591222178487888086158883245 = 64315318495183134971405579840 := by
  rw [← show ((([(3, 1), (5, 1), (6210646456541, 1), (1294457005104863, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_6210646456541, prime_oneHundredTwoCV_1294457005104863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883246 : Nat.totient 120591222178487888086158883246 = 60169732986657611677774259448 := by
  rw [← show ((([(2, 1), (479, 1), (582532365739, 1), (216087740160283, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_479, prime_oneHundredTwoCV_582532365739, prime_oneHundredTwoCV_216087740160283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883247 : Nat.totient 120591222178487888086158883247 = 109622726727373037136430846360 := by
  rw [← show ((([(11, 1), (19379, 1), (565707125231566916794463, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_19379, prime_oneHundredTwoCV_565707125231566916794463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883248 : Nat.totient 120591222178487888086158883248 = 39741454432315961955679827456 := by
  rw [← show ((([(2, 4), (3, 4), (173, 1), (179, 1), (3004772259021847233389, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_173, prime_oneHundredTwoCV_179, prime_oneHundredTwoCV_3004772259021847233389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883249 : Nat.totient 120591222178487888086158883249 = 103363902029409018878967212256 := by
  rw [← show ((([(7, 1), (38353823, 1), (449168195151489808409, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_38353823, prime_oneHundredTwoCV_449168195151489808409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883250 : Nat.totient 120591222178487888086158883250 = 47766505729504758195712838400 := by
  rw [← show ((([(2, 1), (5, 3), (103, 1), (28643, 1), (11834770069, 1), (13815294133, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_103, prime_oneHundredTwoCV_28643, prime_oneHundredTwoCV_11834770069, prime_oneHundredTwoCV_13815294133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883251 : Nat.totient 120591222178487888086158883251 = 80394148118989925815920008552 := by
  rw [← show ((([(3, 1), (41967244831139, 1), (957820181459003, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_41967244831139, prime_oneHundredTwoCV_957820181459003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883252 : Nat.totient 120591222178487888086158883252 = 60295611089243944043079441624 := by
  rw [← show ((([(2, 2), (30147805544621972021539720813, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_30147805544621972021539720813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883253 : Nat.totient 120591222178487888086158883253 = 115347033446734815419590921728 := by
  rw [← show ((([(23, 1), (105619, 1), (49641604412615108400769, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_23, prime_oneHundredTwoCV_105619, prime_oneHundredTwoCV_49641604412615108400769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883254 : Nat.totient 120591222178487888086158883254 = 39782666944413003966575800320 := by
  rw [← show ((([(2, 1), (3, 1), (97, 1), (10081711, 1), (115822583, 1), (177445594769, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_97, prime_oneHundredTwoCV_10081711, prime_oneHundredTwoCV_115822583, prime_oneHundredTwoCV_177445594769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883255 : Nat.totient 120591222178487888086158883255 = 96196487326632229176627361920 := by
  rw [← show ((([(5, 1), (349, 1), (1536991, 1), (100409923, 1), (447787851443, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_349, prime_oneHundredTwoCV_1536991, prime_oneHundredTwoCV_100409923, prime_oneHundredTwoCV_447787851443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883256 : Nat.totient 120591222178487888086158883256 = 47706417565116087594524393088 := by
  rw [← show ((([(2, 3), (7, 1), (13, 1), (165647283212208637480987477, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_165647283212208637480987477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883257 : Nat.totient 120591222178487888086158883257 = 75406187697823240607433277440 := by
  rw [← show ((([(3, 2), (17, 1), (443, 1), (857, 1), (10328185009, 1), (201009095291, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_17, prime_oneHundredTwoCV_443, prime_oneHundredTwoCV_857, prime_oneHundredTwoCV_10328185009, prime_oneHundredTwoCV_201009095291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883258 : Nat.totient 120591222178487888086158883258 = 54814191899312676402799492380 := by
  rw [← show ((([(2, 1), (11, 1), (5481419189931267640279949239, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_5481419189931267640279949239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883259 : Nat.totient 120591222178487888086158883259 = 120590641327953609709573080096 := by
  rw [← show ((([(207653, 1), (1037592019, 1), (559694274621637, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_207653, prime_oneHundredTwoCV_1037592019, prime_oneHundredTwoCV_559694274621637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883260 : Nat.totient 120591222178487888086158883260 = 31360957862931726662617270272 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (43, 1), (643, 1), (72691732177467472052129, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_43, prime_oneHundredTwoCV_643, prime_oneHundredTwoCV_72691732177467472052129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883261 : Nat.totient 120591222178487888086158883261 = 113484633812901677953084348800 := by
  rw [← show ((([(19, 1), (211, 1), (521, 1), (57735365187678916337549, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_19, prime_oneHundredTwoCV_211, prime_oneHundredTwoCV_521, prime_oneHundredTwoCV_57735365187678916337549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883262 : Nat.totient 120591222178487888086158883262 = 60295606905196734407003316480 := by
  rw [← show ((([(2, 1), (14419289, 1), (29795121799, 1), (140344917521, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_14419289, prime_oneHundredTwoCV_29795121799, prime_oneHundredTwoCV_140344917521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883263 : Nat.totient 120591222178487888086158883263 = 66685436923754399200598141280 := by
  rw [← show ((([(3, 1), (7, 1), (31, 1), (69959, 1), (2647836198693597078907, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_31, prime_oneHundredTwoCV_69959, prime_oneHundredTwoCV_2647836198693597078907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883264 : Nat.totient 120591222178487888086158883264 = 58176018966771269682946257920 := by
  rw [← show ((([(2, 6), (47, 1), (71, 1), (10499, 1), (53781335241365175077, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_47, prime_oneHundredTwoCV_71, prime_oneHundredTwoCV_10499, prime_oneHundredTwoCV_53781335241365175077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883265 : Nat.totient 120591222178487888086158883265 = 96472491975098918315338082032 := by
  rw [← show ((([(5, 1), (198599, 1), (121441922848038397057547, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_198599, prime_oneHundredTwoCV_121441922848038397057547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883266 : Nat.totient 120591222178487888086158883266 = 40197074059495962695386294416 := by
  rw [← show ((([(2, 1), (3, 2), (6699512343249327115897715737, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_6699512343249327115897715737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883267 : Nat.totient 120591222178487888086158883267 = 118205668279094169790115569704 := by
  rw [← show ((([(59, 1), (347, 1), (5890256541712884681588379, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_59, prime_oneHundredTwoCV_347, prime_oneHundredTwoCV_5890256541712884681588379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883268 : Nat.totient 120591222178487888086158883268 = 60295611089243944043079441632 := by
  rw [← show ((([(2, 2), (30147805544621972021539720817, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_30147805544621972021539720817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883269 : Nat.totient 120591222178487888086158883269 = 67275436873962974207957568000 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (601, 1), (887, 1), (527303085606055416103, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_601, prime_oneHundredTwoCV_887, prime_oneHundredTwoCV_527303085606055416103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883270 : Nat.totient 120591222178487888086158883270 = 39848610522357300406950144000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (29, 1), (733, 1), (4583, 1), (4931, 1), (3586169597226101, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_29, prime_oneHundredTwoCV_733, prime_oneHundredTwoCV_4583, prime_oneHundredTwoCV_4931, prime_oneHundredTwoCV_3586169597226101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883271 : Nat.totient 120591222178487888086158883271 = 120287963347194695799173932800 := by
  rw [← show ((([(401, 1), (47497, 1), (6331478616472686952543, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_401, prime_oneHundredTwoCV_47497, prime_oneHundredTwoCV_6331478616472686952543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883272 : Nat.totient 120591222178487888086158883272 = 39095756307812834569346227200 := by
  rw [← show ((([(2, 3), (3, 1), (37, 1), (3461, 1), (10831, 1), (3622701707592705509, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_37, prime_oneHundredTwoCV_3461, prime_oneHundredTwoCV_10831, prime_oneHundredTwoCV_3622701707592705509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883273 : Nat.totient 120591222178487888086158883273 = 120129390342065020008645659184 := by
  rw [← show ((([(263, 1), (36293, 1), (12633889657307292504547, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_263, prime_oneHundredTwoCV_36293, prime_oneHundredTwoCV_12633889657307292504547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883274 : Nat.totient 120591222178487888086158883274 = 56151723133570555687100620800 := by
  rw [← show ((([(2, 1), (17, 1), (101, 1), (1597, 1), (1600349, 1), (13740286455772937, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_17, prime_oneHundredTwoCV_101, prime_oneHundredTwoCV_1597, prime_oneHundredTwoCV_1600349, prime_oneHundredTwoCV_13740286455772937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883275 : Nat.totient 120591222178487888086158883275 = 64313488910448184260957143040 := by
  rw [← show ((([(3, 3), (5, 2), (35153, 1), (40267055753, 1), (126211710817, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_35153, prime_oneHundredTwoCV_40267055753, prime_oneHundredTwoCV_126211710817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883276 : Nat.totient 120591222178487888086158883276 = 56813255873836603991272774032 := by
  rw [← show ((([(2, 2), (23, 1), (67, 1), (19563793344985056470823959, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_23, prime_oneHundredTwoCV_67, prime_oneHundredTwoCV_19563793344985056470823959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883277 : Nat.totient 120591222178487888086158883277 = 103363821549463977410884560000 := by
  rw [← show ((([(7, 1), (1255021, 1), (126880591, 1), (108186101438201, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_1255021, prime_oneHundredTwoCV_126880591, prime_oneHundredTwoCV_108186101438201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883278 : Nat.totient 120591222178487888086158883278 = 39474532932465944553754429440 := by
  rw [← show ((([(2, 1), (3, 1), (73, 1), (281, 1), (1283, 1), (2740733, 1), (278638985960059, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_73, prime_oneHundredTwoCV_281, prime_oneHundredTwoCV_1283, prime_oneHundredTwoCV_2740733, prime_oneHundredTwoCV_278638985960059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883279 : Nat.totient 120591222178487888086158883279 = 119588553111182867071754284800 := by
  rw [← show ((([(131, 1), (1481, 1), (105229, 1), (646619, 1), (9134934499139, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_131, prime_oneHundredTwoCV_1481, prime_oneHundredTwoCV_105229, prime_oneHundredTwoCV_646619, prime_oneHundredTwoCV_9134934499139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883280 : Nat.totient 120591222178487888086158883280 = 41541402133886938073826140160 := by
  rw [← show ((([(2, 4), (5, 1), (11, 1), (19, 1), (21107, 1), (2417603, 1), (141340924460369, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_19, prime_oneHundredTwoCV_21107, prime_oneHundredTwoCV_2417603, prime_oneHundredTwoCV_141340924460369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883281 : Nat.totient 120591222178487888086158883281 = 78757573871146231475189484800 := by
  rw [← show ((([(3, 1), (53, 1), (659, 1), (8980079, 1), (33380351, 1), (3839388869, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_53, prime_oneHundredTwoCV_659, prime_oneHundredTwoCV_8980079, prime_oneHundredTwoCV_33380351, prime_oneHundredTwoCV_3839388869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883282 : Nat.totient 120591222178487888086158883282 = 55657395427733449070120278992 := by
  rw [← show ((([(2, 1), (13, 1), (606743, 1), (7644297387760290352699, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_606743, prime_oneHundredTwoCV_7644297387760290352699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883283 : Nat.totient 120591222178487888086158883283 = 117649938942875403826747765120 := by
  rw [← show ((([(41, 1), (3469049, 1), (847854648760087809587, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_41, prime_oneHundredTwoCV_3469049, prime_oneHundredTwoCV_847854648760087809587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883284 : Nat.totient 120591222178487888086158883284 = 34197076869991254109932687360 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (137, 1), (5641, 1), (32850247, 1), (18849500653133, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_137, prime_oneHundredTwoCV_5641, prime_oneHundredTwoCV_32850247, prime_oneHundredTwoCV_18849500653133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883285 : Nat.totient 120591222178487888086158883285 = 96463429470409898582552655360 := by
  rw [← show ((([(5, 1), (10141, 1), (2747449, 1), (865635921489004973, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_10141, prime_oneHundredTwoCV_2747449, prime_oneHundredTwoCV_865635921489004973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883286 : Nat.totient 120591222178487888086158883286 = 60295611089243944043079441642 := by
  rw [← show ((([(2, 1), (60295611089243944043079441643, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_60295611089243944043079441643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883287 : Nat.totient 120591222178487888086158883287 = 79076211264582221695841890560 := by
  rw [← show ((([(3, 1), (61, 1), (658968427204851847465349089, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_61, prime_oneHundredTwoCV_658968427204851847465349089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883288 : Nat.totient 120591222178487888086158883288 = 60254766890293350161065881600 := by
  rw [← show ((([(2, 3), (1487, 1), (207709, 1), (10738801, 1), (4544683376617, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_1487, prime_oneHundredTwoCV_207709, prime_oneHundredTwoCV_10738801, prime_oneHundredTwoCV_4544683376617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883289 : Nat.totient 120591222178487888086158883289 = 120155874795845822312013761136 := by
  rw [← show ((([(277, 1), (11830386719, 1), (36799082128594603, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_277, prime_oneHundredTwoCV_11830386719, prime_oneHundredTwoCV_36799082128594603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883290 : Nat.totient 120591222178487888086158883290 = 32157438712736713394981417280 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (145819, 1), (9159367771, 1), (3009641931707, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_145819, prime_oneHundredTwoCV_9159367771, prime_oneHundredTwoCV_3009641931707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883291 : Nat.totient 120591222178487888086158883291 = 87051271504003056699950592000 := by
  rw [← show ((([(7, 2), (11, 1), (17, 1), (151, 1), (157, 1), (359, 1), (1546347020427381989, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_11, prime_oneHundredTwoCV_17, prime_oneHundredTwoCV_151, prime_oneHundredTwoCV_157, prime_oneHundredTwoCV_359, prime_oneHundredTwoCV_1546347020427381989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883292 : Nat.totient 120591222178487888086158883292 = 60295611089243944043079441644 := by
  rw [← show ((([(2, 2), (30147805544621972021539720823, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_30147805544621972021539720823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883293 : Nat.totient 120591222178487888086158883293 = 80394147284788557486901776960 := by
  rw [← show ((([(3, 2), (96372361, 1), (139033894650548762957, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_96372361, prime_oneHundredTwoCV_139033894650548762957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883294 : Nat.totient 120591222178487888086158883294 = 58345689201490116777342154680 := by
  rw [← show ((([(2, 1), (31, 1), (11903, 1), (163405839919033542758479, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_31, prime_oneHundredTwoCV_11903, prime_oneHundredTwoCV_163405839919033542758479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883295 : Nat.totient 120591222178487888086158883295 = 89051979454878463896172155264 := by
  rw [← show ((([(5, 1), (13, 1), (23658976647589, 1), (78416306825587, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_13, prime_oneHundredTwoCV_23658976647589, prime_oneHundredTwoCV_78416306825587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883296 : Nat.totient 120591222178487888086158883296 = 40059882680453314358541963264 := by
  rw [← show ((([(2, 5), (3, 1), (293, 1), (4287230595082760526385057, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_293, prime_oneHundredTwoCV_4287230595082760526385057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883297 : Nat.totient 120591222178487888086158883297 = 119924972332197899754191154480 := by
  rw [← show ((([(181, 1), (666249846289988331967728637, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_181, prime_oneHundredTwoCV_666249846289988331967728637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883298 : Nat.totient 120591222178487888086158883298 = 51523928695425329607892982400 := by
  rw [← show ((([(2, 1), (7, 1), (331, 1), (27337, 1), (951938330765685269581, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_7, prime_oneHundredTwoCV_331, prime_oneHundredTwoCV_27337, prime_oneHundredTwoCV_951938330765685269581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883299 : Nat.totient 120591222178487888086158883299 = 69982274407278129234862487040 := by
  rw [← show ((([(3, 1), (19, 1), (23, 1), (29, 1), (197, 1), (35018183, 1), (459785396206571, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_3, prime_oneHundredTwoCV_19, prime_oneHundredTwoCV_23, prime_oneHundredTwoCV_29, prime_oneHundredTwoCV_197, prime_oneHundredTwoCV_35018183, prime_oneHundredTwoCV_459785396206571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883300 : Nat.totient 120591222178487888086158883300 = 48236408039271647033914446720 := by
  rw [← show ((([(2, 2), (5, 2), (596749, 1), (2020803087705013130917, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_2, prime_oneHundredTwoCV_5, prime_oneHundredTwoCV_596749, prime_oneHundredTwoCV_2020803087705013130917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwoCV_120591222178487888086158883301 : Nat.totient 120591222178487888086158883301 = 119063444942927040622888880448 := by
  rw [← show ((([(79, 1), (91163, 1), (28929483469, 1), (578801059477, 1)] : List FactorBlock).map factorBlockValue).prod) = 120591222178487888086158883301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwoCV_79, prime_oneHundredTwoCV_91163, prime_oneHundredTwoCV_28929483469, prime_oneHundredTwoCV_578801059477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwoCV : certifiedKill 1 120591222178487888086158883199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwoCV_120591222178487888086158883200, phi_oneHundredTwoCV_120591222178487888086158883201, phi_oneHundredTwoCV_120591222178487888086158883202,
    phi_oneHundredTwoCV_120591222178487888086158883203, phi_oneHundredTwoCV_120591222178487888086158883204, phi_oneHundredTwoCV_120591222178487888086158883205,
    phi_oneHundredTwoCV_120591222178487888086158883206, phi_oneHundredTwoCV_120591222178487888086158883207, phi_oneHundredTwoCV_120591222178487888086158883208,
    phi_oneHundredTwoCV_120591222178487888086158883209, phi_oneHundredTwoCV_120591222178487888086158883210, phi_oneHundredTwoCV_120591222178487888086158883211,
    phi_oneHundredTwoCV_120591222178487888086158883212, phi_oneHundredTwoCV_120591222178487888086158883213, phi_oneHundredTwoCV_120591222178487888086158883214,
    phi_oneHundredTwoCV_120591222178487888086158883215, phi_oneHundredTwoCV_120591222178487888086158883216, phi_oneHundredTwoCV_120591222178487888086158883217,
    phi_oneHundredTwoCV_120591222178487888086158883218, phi_oneHundredTwoCV_120591222178487888086158883219, phi_oneHundredTwoCV_120591222178487888086158883220,
    phi_oneHundredTwoCV_120591222178487888086158883221, phi_oneHundredTwoCV_120591222178487888086158883222, phi_oneHundredTwoCV_120591222178487888086158883223,
    phi_oneHundredTwoCV_120591222178487888086158883224, phi_oneHundredTwoCV_120591222178487888086158883225, phi_oneHundredTwoCV_120591222178487888086158883226,
    phi_oneHundredTwoCV_120591222178487888086158883227, phi_oneHundredTwoCV_120591222178487888086158883228, phi_oneHundredTwoCV_120591222178487888086158883229,
    phi_oneHundredTwoCV_120591222178487888086158883230, phi_oneHundredTwoCV_120591222178487888086158883231, phi_oneHundredTwoCV_120591222178487888086158883232,
    phi_oneHundredTwoCV_120591222178487888086158883233, phi_oneHundredTwoCV_120591222178487888086158883234, phi_oneHundredTwoCV_120591222178487888086158883235,
    phi_oneHundredTwoCV_120591222178487888086158883236, phi_oneHundredTwoCV_120591222178487888086158883237, phi_oneHundredTwoCV_120591222178487888086158883238,
    phi_oneHundredTwoCV_120591222178487888086158883239, phi_oneHundredTwoCV_120591222178487888086158883240, phi_oneHundredTwoCV_120591222178487888086158883241,
    phi_oneHundredTwoCV_120591222178487888086158883242, phi_oneHundredTwoCV_120591222178487888086158883243, phi_oneHundredTwoCV_120591222178487888086158883244,
    phi_oneHundredTwoCV_120591222178487888086158883245, phi_oneHundredTwoCV_120591222178487888086158883246, phi_oneHundredTwoCV_120591222178487888086158883247,
    phi_oneHundredTwoCV_120591222178487888086158883248, phi_oneHundredTwoCV_120591222178487888086158883249, phi_oneHundredTwoCV_120591222178487888086158883250,
    phi_oneHundredTwoCV_120591222178487888086158883251, phi_oneHundredTwoCV_120591222178487888086158883252, phi_oneHundredTwoCV_120591222178487888086158883253,
    phi_oneHundredTwoCV_120591222178487888086158883254, phi_oneHundredTwoCV_120591222178487888086158883255, phi_oneHundredTwoCV_120591222178487888086158883256,
    phi_oneHundredTwoCV_120591222178487888086158883257, phi_oneHundredTwoCV_120591222178487888086158883258, phi_oneHundredTwoCV_120591222178487888086158883259,
    phi_oneHundredTwoCV_120591222178487888086158883260, phi_oneHundredTwoCV_120591222178487888086158883261, phi_oneHundredTwoCV_120591222178487888086158883262,
    phi_oneHundredTwoCV_120591222178487888086158883263, phi_oneHundredTwoCV_120591222178487888086158883264, phi_oneHundredTwoCV_120591222178487888086158883265,
    phi_oneHundredTwoCV_120591222178487888086158883266, phi_oneHundredTwoCV_120591222178487888086158883267, phi_oneHundredTwoCV_120591222178487888086158883268,
    phi_oneHundredTwoCV_120591222178487888086158883269, phi_oneHundredTwoCV_120591222178487888086158883270, phi_oneHundredTwoCV_120591222178487888086158883271,
    phi_oneHundredTwoCV_120591222178487888086158883272, phi_oneHundredTwoCV_120591222178487888086158883273, phi_oneHundredTwoCV_120591222178487888086158883274,
    phi_oneHundredTwoCV_120591222178487888086158883275, phi_oneHundredTwoCV_120591222178487888086158883276, phi_oneHundredTwoCV_120591222178487888086158883277,
    phi_oneHundredTwoCV_120591222178487888086158883278, phi_oneHundredTwoCV_120591222178487888086158883279, phi_oneHundredTwoCV_120591222178487888086158883280,
    phi_oneHundredTwoCV_120591222178487888086158883281, phi_oneHundredTwoCV_120591222178487888086158883282, phi_oneHundredTwoCV_120591222178487888086158883283,
    phi_oneHundredTwoCV_120591222178487888086158883284, phi_oneHundredTwoCV_120591222178487888086158883285, phi_oneHundredTwoCV_120591222178487888086158883286,
    phi_oneHundredTwoCV_120591222178487888086158883287, phi_oneHundredTwoCV_120591222178487888086158883288, phi_oneHundredTwoCV_120591222178487888086158883289,
    phi_oneHundredTwoCV_120591222178487888086158883290, phi_oneHundredTwoCV_120591222178487888086158883291, phi_oneHundredTwoCV_120591222178487888086158883292,
    phi_oneHundredTwoCV_120591222178487888086158883293, phi_oneHundredTwoCV_120591222178487888086158883294, phi_oneHundredTwoCV_120591222178487888086158883295,
    phi_oneHundredTwoCV_120591222178487888086158883296, phi_oneHundredTwoCV_120591222178487888086158883297, phi_oneHundredTwoCV_120591222178487888086158883298,
    phi_oneHundredTwoCV_120591222178487888086158883299, phi_oneHundredTwoCV_120591222178487888086158883300, phi_oneHundredTwoCV_120591222178487888086158883301
    ]

end TotientTailPeriodKiller
end Erdos249257
