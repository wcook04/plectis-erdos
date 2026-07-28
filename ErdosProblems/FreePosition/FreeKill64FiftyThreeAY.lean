import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 53P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyThreeAYFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyThreeAYFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyThreeAYFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyThreeAYFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyThreeAYFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyThreeAYFastPow a n * fiftyThreeAYFastPow a n * a
        else fiftyThreeAYFastPow a n * fiftyThreeAYFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyThreeAY_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyThreeAY_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyThreeAY_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyThreeAY_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyThreeAY_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyThreeAY_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyThreeAY_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyThreeAY_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyThreeAY_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyThreeAY_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyThreeAY_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyThreeAY_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyThreeAY_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyThreeAY_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyThreeAY_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyThreeAY_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyThreeAY_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyThreeAY_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyThreeAY_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyThreeAY_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyThreeAY_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyThreeAY_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyThreeAY_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyThreeAY_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyThreeAY_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyThreeAY_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyThreeAY_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyThreeAY_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyThreeAY_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyThreeAY_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyThreeAY_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyThreeAY_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyThreeAY_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyThreeAY_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftyThreeAY_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyThreeAY_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyThreeAY_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyThreeAY_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyThreeAY_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyThreeAY_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyThreeAY_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyThreeAY_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyThreeAY_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyThreeAY_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftyThreeAY_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftyThreeAY_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyThreeAY_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyThreeAY_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyThreeAY_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyThreeAY_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftyThreeAY_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyThreeAY_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftyThreeAY_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyThreeAY_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftyThreeAY_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyThreeAY_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyThreeAY_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyThreeAY_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftyThreeAY_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftyThreeAY_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftyThreeAY_313 : Nat.Prime 313 := by norm_num
private theorem prime_fiftyThreeAY_337 : Nat.Prime 337 := by norm_num
private theorem prime_fiftyThreeAY_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftyThreeAY_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftyThreeAY_373 : Nat.Prime 373 := by norm_num
private theorem prime_fiftyThreeAY_379 : Nat.Prime 379 := by norm_num
private theorem prime_fiftyThreeAY_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyThreeAY_389 : Nat.Prime 389 := by norm_num
private theorem prime_fiftyThreeAY_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyThreeAY_431 : Nat.Prime 431 := by norm_num
private theorem prime_fiftyThreeAY_439 : Nat.Prime 439 := by norm_num
private theorem prime_fiftyThreeAY_443 : Nat.Prime 443 := by norm_num
private theorem prime_fiftyThreeAY_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftyThreeAY_457 : Nat.Prime 457 := by norm_num
private theorem prime_fiftyThreeAY_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftyThreeAY_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftyThreeAY_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyThreeAY_491 : Nat.Prime 491 := by norm_num
private theorem prime_fiftyThreeAY_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftyThreeAY_523 : Nat.Prime 523 := by norm_num
private theorem prime_fiftyThreeAY_547 : Nat.Prime 547 := by norm_num
private theorem prime_fiftyThreeAY_569 : Nat.Prime 569 := by norm_num
private theorem prime_fiftyThreeAY_577 : Nat.Prime 577 := by norm_num
private theorem prime_fiftyThreeAY_587 : Nat.Prime 587 := by norm_num
private theorem prime_fiftyThreeAY_599 : Nat.Prime 599 := by norm_num
private theorem prime_fiftyThreeAY_601 : Nat.Prime 601 := by norm_num
private theorem prime_fiftyThreeAY_619 : Nat.Prime 619 := by norm_num
private theorem prime_fiftyThreeAY_647 : Nat.Prime 647 := by norm_num
private theorem prime_fiftyThreeAY_661 : Nat.Prime 661 := by norm_num
private theorem prime_fiftyThreeAY_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftyThreeAY_683 : Nat.Prime 683 := by norm_num
private theorem prime_fiftyThreeAY_691 : Nat.Prime 691 := by norm_num
private theorem prime_fiftyThreeAY_701 : Nat.Prime 701 := by norm_num
private theorem prime_fiftyThreeAY_709 : Nat.Prime 709 := by norm_num
private theorem prime_fiftyThreeAY_733 : Nat.Prime 733 := by norm_num
private theorem prime_fiftyThreeAY_751 : Nat.Prime 751 := by norm_num
private theorem prime_fiftyThreeAY_757 : Nat.Prime 757 := by norm_num
private theorem prime_fiftyThreeAY_811 : Nat.Prime 811 := by norm_num
private theorem prime_fiftyThreeAY_829 : Nat.Prime 829 := by norm_num
private theorem prime_fiftyThreeAY_853 : Nat.Prime 853 := by norm_num
private theorem prime_fiftyThreeAY_859 : Nat.Prime 859 := by norm_num
private theorem prime_fiftyThreeAY_883 : Nat.Prime 883 := by norm_num
private theorem prime_fiftyThreeAY_947 : Nat.Prime 947 := by norm_num
private theorem prime_fiftyThreeAY_983 : Nat.Prime 983 := by norm_num
private theorem prime_fiftyThreeAY_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fiftyThreeAY_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_fiftyThreeAY_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fiftyThreeAY_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_fiftyThreeAY_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_fiftyThreeAY_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_fiftyThreeAY_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fiftyThreeAY_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fiftyThreeAY_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fiftyThreeAY_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fiftyThreeAY_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_fiftyThreeAY_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_fiftyThreeAY_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_fiftyThreeAY_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_fiftyThreeAY_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_fiftyThreeAY_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fiftyThreeAY_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_fiftyThreeAY_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fiftyThreeAY_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_fiftyThreeAY_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fiftyThreeAY_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_fiftyThreeAY_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_fiftyThreeAY_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fiftyThreeAY_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_fiftyThreeAY_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_fiftyThreeAY_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_fiftyThreeAY_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_fiftyThreeAY_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_fiftyThreeAY_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_fiftyThreeAY_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_fiftyThreeAY_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_fiftyThreeAY_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_fiftyThreeAY_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_fiftyThreeAY_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_fiftyThreeAY_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_fiftyThreeAY_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_fiftyThreeAY_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_fiftyThreeAY_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_fiftyThreeAY_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_fiftyThreeAY_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fiftyThreeAY_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_fiftyThreeAY_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_fiftyThreeAY_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_fiftyThreeAY_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_fiftyThreeAY_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_fiftyThreeAY_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fiftyThreeAY_2909 : Nat.Prime 2909 := by norm_num
private theorem prime_fiftyThreeAY_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_fiftyThreeAY_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_fiftyThreeAY_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_fiftyThreeAY_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_fiftyThreeAY_3391 : Nat.Prime 3391 := by norm_num
private theorem prime_fiftyThreeAY_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_fiftyThreeAY_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_fiftyThreeAY_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_fiftyThreeAY_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_fiftyThreeAY_3919 : Nat.Prime 3919 := by norm_num
private theorem prime_fiftyThreeAY_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_fiftyThreeAY_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_fiftyThreeAY_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_fiftyThreeAY_4391 : Nat.Prime 4391 := by norm_num
private theorem prime_fiftyThreeAY_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_fiftyThreeAY_4751 : Nat.Prime 4751 := by norm_num
private theorem prime_fiftyThreeAY_4793 : Nat.Prime 4793 := by norm_num
private theorem prime_fiftyThreeAY_4799 : Nat.Prime 4799 := by norm_num
private theorem prime_fiftyThreeAY_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_fiftyThreeAY_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftyThreeAY_5101 : Nat.Prime 5101 := by norm_num
private theorem prime_fiftyThreeAY_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_fiftyThreeAY_5399 : Nat.Prime 5399 := by norm_num
private theorem prime_fiftyThreeAY_5519 : Nat.Prime 5519 := by norm_num
private theorem prime_fiftyThreeAY_5693 : Nat.Prime 5693 := by norm_num
private theorem prime_fiftyThreeAY_5813 : Nat.Prime 5813 := by norm_num
private theorem prime_fiftyThreeAY_5861 : Nat.Prime 5861 := by norm_num
private theorem prime_fiftyThreeAY_5869 : Nat.Prime 5869 := by norm_num
private theorem prime_fiftyThreeAY_5981 : Nat.Prime 5981 := by norm_num
private theorem prime_fiftyThreeAY_6011 : Nat.Prime 6011 := by norm_num
private theorem prime_fiftyThreeAY_6113 : Nat.Prime 6113 := by norm_num
private theorem prime_fiftyThreeAY_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_fiftyThreeAY_6367 : Nat.Prime 6367 := by norm_num
private theorem prime_fiftyThreeAY_6619 : Nat.Prime 6619 := by norm_num
private theorem prime_fiftyThreeAY_6823 : Nat.Prime 6823 := by norm_num
private theorem prime_fiftyThreeAY_6869 : Nat.Prime 6869 := by norm_num
private theorem prime_fiftyThreeAY_6907 : Nat.Prime 6907 := by norm_num
private theorem prime_fiftyThreeAY_7499 : Nat.Prime 7499 := by norm_num
private theorem prime_fiftyThreeAY_7717 : Nat.Prime 7717 := by norm_num
private theorem prime_fiftyThreeAY_7753 : Nat.Prime 7753 := by norm_num
private theorem prime_fiftyThreeAY_7793 : Nat.Prime 7793 := by norm_num
private theorem prime_fiftyThreeAY_8291 : Nat.Prime 8291 := by norm_num
private theorem prime_fiftyThreeAY_8467 : Nat.Prime 8467 := by norm_num
private theorem prime_fiftyThreeAY_8581 : Nat.Prime 8581 := by norm_num
private theorem prime_fiftyThreeAY_8933 : Nat.Prime 8933 := by norm_num
private theorem prime_fiftyThreeAY_9127 : Nat.Prime 9127 := by norm_num
private theorem prime_fiftyThreeAY_9533 : Nat.Prime 9533 := by norm_num
private theorem prime_fiftyThreeAY_9619 : Nat.Prime 9619 := by norm_num
private theorem prime_fiftyThreeAY_9623 : Nat.Prime 9623 := by norm_num
private theorem prime_fiftyThreeAY_9689 : Nat.Prime 9689 := by norm_num
private theorem prime_fiftyThreeAY_9883 : Nat.Prime 9883 := by norm_num
private theorem prime_fiftyThreeAY_9887 : Nat.Prime 9887 := by norm_num
private theorem prime_fiftyThreeAY_10039 : Nat.Prime 10039 := by norm_num
private theorem prime_fiftyThreeAY_10667 : Nat.Prime 10667 := by norm_num
private theorem prime_fiftyThreeAY_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_fiftyThreeAY_10771 : Nat.Prime 10771 := by norm_num
private theorem prime_fiftyThreeAY_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_fiftyThreeAY_11299 : Nat.Prime 11299 := by norm_num
private theorem prime_fiftyThreeAY_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_fiftyThreeAY_11743 : Nat.Prime 11743 := by norm_num
private theorem prime_fiftyThreeAY_11777 : Nat.Prime 11777 := by norm_num
private theorem prime_fiftyThreeAY_13037 : Nat.Prime 13037 := by norm_num
private theorem prime_fiftyThreeAY_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_fiftyThreeAY_14153 : Nat.Prime 14153 := by norm_num
private theorem prime_fiftyThreeAY_14221 : Nat.Prime 14221 := by norm_num
private theorem prime_fiftyThreeAY_14389 : Nat.Prime 14389 := by norm_num
private theorem prime_fiftyThreeAY_14747 : Nat.Prime 14747 := by norm_num
private theorem prime_fiftyThreeAY_14767 : Nat.Prime 14767 := by norm_num
private theorem prime_fiftyThreeAY_15263 : Nat.Prime 15263 := by norm_num
private theorem prime_fiftyThreeAY_15427 : Nat.Prime 15427 := by norm_num
private theorem prime_fiftyThreeAY_15803 : Nat.Prime 15803 := by norm_num
private theorem prime_fiftyThreeAY_16273 : Nat.Prime 16273 := by norm_num
private theorem prime_fiftyThreeAY_16363 : Nat.Prime 16363 := by norm_num
private theorem prime_fiftyThreeAY_16381 : Nat.Prime 16381 := by norm_num
private theorem prime_fiftyThreeAY_17299 : Nat.Prime 17299 := by norm_num
private theorem prime_fiftyThreeAY_17387 : Nat.Prime 17387 := by norm_num
private theorem prime_fiftyThreeAY_17597 : Nat.Prime 17597 := by norm_num
private theorem prime_fiftyThreeAY_19681 : Nat.Prime 19681 := by norm_num
private theorem prime_fiftyThreeAY_19937 : Nat.Prime 19937 := by norm_num
private theorem prime_fiftyThreeAY_20051 : Nat.Prime 20051 := by norm_num
private theorem prime_fiftyThreeAY_21107 : Nat.Prime 21107 := by norm_num
private theorem prime_fiftyThreeAY_21803 : Nat.Prime 21803 := by norm_num
private theorem prime_fiftyThreeAY_23599 : Nat.Prime 23599 := by norm_num
private theorem prime_fiftyThreeAY_23873 : Nat.Prime 23873 := by norm_num
private theorem prime_fiftyThreeAY_24623 : Nat.Prime 24623 := by norm_num
private theorem prime_fiftyThreeAY_25603 : Nat.Prime 25603 := by norm_num
private theorem prime_fiftyThreeAY_27883 : Nat.Prime 27883 := by norm_num
private theorem prime_fiftyThreeAY_27901 : Nat.Prime 27901 := by norm_num
private theorem prime_fiftyThreeAY_28477 : Nat.Prime 28477 := by norm_num
private theorem prime_fiftyThreeAY_30497 : Nat.Prime 30497 := by norm_num
private theorem prime_fiftyThreeAY_31771 : Nat.Prime 31771 := by norm_num
private theorem prime_fiftyThreeAY_32363 : Nat.Prime 32363 := by norm_num
private theorem prime_fiftyThreeAY_32533 : Nat.Prime 32533 := by norm_num
private theorem prime_fiftyThreeAY_34057 : Nat.Prime 34057 := by norm_num
private theorem prime_fiftyThreeAY_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fiftyThreeAY_35401 : Nat.Prime 35401 := by norm_num
private theorem prime_fiftyThreeAY_35671 : Nat.Prime 35671 := by norm_num
private theorem prime_fiftyThreeAY_35899 : Nat.Prime 35899 := by norm_num
private theorem prime_fiftyThreeAY_35963 : Nat.Prime 35963 := by norm_num
private theorem prime_fiftyThreeAY_36191 : Nat.Prime 36191 := by norm_num
private theorem prime_fiftyThreeAY_38069 : Nat.Prime 38069 := by norm_num
private theorem prime_fiftyThreeAY_38201 : Nat.Prime 38201 := by norm_num
private theorem prime_fiftyThreeAY_38351 : Nat.Prime 38351 := by norm_num
private theorem prime_fiftyThreeAY_39341 : Nat.Prime 39341 := by norm_num
private theorem prime_fiftyThreeAY_39827 : Nat.Prime 39827 := by norm_num
private theorem prime_fiftyThreeAY_41411 : Nat.Prime 41411 := by norm_num
private theorem prime_fiftyThreeAY_42787 : Nat.Prime 42787 := by norm_num
private theorem prime_fiftyThreeAY_44533 : Nat.Prime 44533 := by norm_num
private theorem prime_fiftyThreeAY_47017 : Nat.Prime 47017 := by norm_num
private theorem prime_fiftyThreeAY_55733 : Nat.Prime 55733 := by norm_num
private theorem prime_fiftyThreeAY_56479 : Nat.Prime 56479 := by norm_num
private theorem prime_fiftyThreeAY_58067 : Nat.Prime 58067 := by norm_num
private theorem prime_fiftyThreeAY_58369 : Nat.Prime 58369 := by norm_num
private theorem prime_fiftyThreeAY_58997 : Nat.Prime 58997 := by norm_num
private theorem prime_fiftyThreeAY_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fiftyThreeAY_61987 : Nat.Prime 61987 := by norm_num
private theorem prime_fiftyThreeAY_63439 : Nat.Prime 63439 := by norm_num
private theorem prime_fiftyThreeAY_63913 : Nat.Prime 63913 := by norm_num
private theorem prime_fiftyThreeAY_65123 : Nat.Prime 65123 := by norm_num
private theorem prime_fiftyThreeAY_65551 : Nat.Prime 65551 := by norm_num
private theorem prime_fiftyThreeAY_66137 : Nat.Prime 66137 := by norm_num
private theorem prime_fiftyThreeAY_67567 : Nat.Prime 67567 := by norm_num
private theorem prime_fiftyThreeAY_67619 : Nat.Prime 67619 := by norm_num
private theorem prime_fiftyThreeAY_68687 : Nat.Prime 68687 := by norm_num
private theorem prime_fiftyThreeAY_69821 : Nat.Prime 69821 := by norm_num
private theorem prime_fiftyThreeAY_73291 : Nat.Prime 73291 := by norm_num
private theorem prime_fiftyThreeAY_77023 : Nat.Prime 77023 := by norm_num
private theorem prime_fiftyThreeAY_80239 : Nat.Prime 80239 := by norm_num
private theorem prime_fiftyThreeAY_80737 : Nat.Prime 80737 := by norm_num
private theorem prime_fiftyThreeAY_80933 : Nat.Prime 80933 := by norm_num
private theorem prime_fiftyThreeAY_81197 : Nat.Prime 81197 := by norm_num
private theorem prime_fiftyThreeAY_85027 : Nat.Prime 85027 := by norm_num
private theorem prime_fiftyThreeAY_86341 : Nat.Prime 86341 := by norm_num
private theorem prime_fiftyThreeAY_89213 : Nat.Prime 89213 := by norm_num
private theorem prime_fiftyThreeAY_90239 : Nat.Prime 90239 := by norm_num
private theorem prime_fiftyThreeAY_90469 : Nat.Prime 90469 := by norm_num
private theorem prime_fiftyThreeAY_95369 : Nat.Prime 95369 := by norm_num
private theorem prime_fiftyThreeAY_98573 : Nat.Prime 98573 := by norm_num
private theorem prime_fiftyThreeAY_102001 : Nat.Prime 102001 := by norm_num
private theorem prime_fiftyThreeAY_106747 : Nat.Prime 106747 := by norm_num
private theorem prime_fiftyThreeAY_108943 : Nat.Prime 108943 := by norm_num
private theorem prime_fiftyThreeAY_109579 : Nat.Prime 109579 := by norm_num
private theorem prime_fiftyThreeAY_114167 : Nat.Prime 114167 := by norm_num
private theorem prime_fiftyThreeAY_119551 : Nat.Prime 119551 := by norm_num
private theorem prime_fiftyThreeAY_121151 : Nat.Prime 121151 := by norm_num
private theorem prime_fiftyThreeAY_124577 : Nat.Prime 124577 := by norm_num
private theorem prime_fiftyThreeAY_129221 : Nat.Prime 129221 := by norm_num
private theorem prime_fiftyThreeAY_132817 : Nat.Prime 132817 := by norm_num
private theorem prime_fiftyThreeAY_134333 : Nat.Prime 134333 := by norm_num
private theorem prime_fiftyThreeAY_135181 : Nat.Prime 135181 := by norm_num
private theorem prime_fiftyThreeAY_140263 : Nat.Prime 140263 := by norm_num
private theorem prime_fiftyThreeAY_141833 : Nat.Prime 141833 := by norm_num
private theorem prime_fiftyThreeAY_143261 : Nat.Prime 143261 := by norm_num
private theorem prime_fiftyThreeAY_146513 : Nat.Prime 146513 := by norm_num
private theorem prime_fiftyThreeAY_148723 : Nat.Prime 148723 := by norm_num
private theorem prime_fiftyThreeAY_152809 : Nat.Prime 152809 := by norm_num
private theorem prime_fiftyThreeAY_152993 : Nat.Prime 152993 := by norm_num
private theorem prime_fiftyThreeAY_164653 : Nat.Prime 164653 := by norm_num
private theorem prime_fiftyThreeAY_166781 : Nat.Prime 166781 := by norm_num
private theorem prime_fiftyThreeAY_166823 : Nat.Prime 166823 := by norm_num
private theorem prime_fiftyThreeAY_170953 : Nat.Prime 170953 := by norm_num
private theorem prime_fiftyThreeAY_176629 : Nat.Prime 176629 := by norm_num
private theorem prime_fiftyThreeAY_189853 : Nat.Prime 189853 := by norm_num
private theorem prime_fiftyThreeAY_193057 : Nat.Prime 193057 := by norm_num
private theorem prime_fiftyThreeAY_221713 : Nat.Prime 221713 := by norm_num
private theorem prime_fiftyThreeAY_223711 : Nat.Prime 223711 := by norm_num
private theorem prime_fiftyThreeAY_231923 : Nat.Prime 231923 := by norm_num
private theorem prime_fiftyThreeAY_240607 : Nat.Prime 240607 := by norm_num
private theorem prime_fiftyThreeAY_246209 : Nat.Prime 246209 := by norm_num
private theorem prime_fiftyThreeAY_259429 : Nat.Prime 259429 := by norm_num
private theorem prime_fiftyThreeAY_259631 : Nat.Prime 259631 := by norm_num
private theorem prime_fiftyThreeAY_259967 : Nat.Prime 259967 := by norm_num
private theorem prime_fiftyThreeAY_260419 : Nat.Prime 260419 := by norm_num
private theorem prime_fiftyThreeAY_284483 : Nat.Prime 284483 := by norm_num
private theorem prime_fiftyThreeAY_303217 : Nat.Prime 303217 := by norm_num
private theorem prime_fiftyThreeAY_310361 : Nat.Prime 310361 := by norm_num
private theorem prime_fiftyThreeAY_327319 : Nat.Prime 327319 := by norm_num
private theorem prime_fiftyThreeAY_338423 : Nat.Prime 338423 := by norm_num
private theorem prime_fiftyThreeAY_353011 : Nat.Prime 353011 := by norm_num
private theorem prime_fiftyThreeAY_367277 : Nat.Prime 367277 := by norm_num
private theorem prime_fiftyThreeAY_391019 : Nat.Prime 391019 := by norm_num
private theorem prime_fiftyThreeAY_429109 : Nat.Prime 429109 := by norm_num
private theorem prime_fiftyThreeAY_462643 : Nat.Prime 462643 := by norm_num
private theorem prime_fiftyThreeAY_501271 : Nat.Prime 501271 := by norm_num
private theorem prime_fiftyThreeAY_512921 : Nat.Prime 512921 := by norm_num
private theorem prime_fiftyThreeAY_520967 : Nat.Prime 520967 := by norm_num
private theorem prime_fiftyThreeAY_637841 : Nat.Prime 637841 := by norm_num
private theorem prime_fiftyThreeAY_641317 : Nat.Prime 641317 := by norm_num
private theorem prime_fiftyThreeAY_658309 : Nat.Prime 658309 := by norm_num
private theorem prime_fiftyThreeAY_700387 : Nat.Prime 700387 := by norm_num
private theorem prime_fiftyThreeAY_705521 : Nat.Prime 705521 := by norm_num
private theorem prime_fiftyThreeAY_758521 : Nat.Prime 758521 := by norm_num
private theorem prime_fiftyThreeAY_772657 : Nat.Prime 772657 := by norm_num
private theorem prime_fiftyThreeAY_779591 : Nat.Prime 779591 := by norm_num
private theorem prime_fiftyThreeAY_847361 : Nat.Prime 847361 := by norm_num
private theorem prime_fiftyThreeAY_865819 : Nat.Prime 865819 := by norm_num
private theorem prime_fiftyThreeAY_939823 : Nat.Prime 939823 := by norm_num
private theorem prime_fiftyThreeAY_984421 : Nat.Prime 984421 := by norm_num
private theorem prime_fiftyThreeAY_1001831 : Nat.Prime 1001831 := by norm_num
private theorem prime_fiftyThreeAY_1079933 : Nat.Prime 1079933 := by norm_num
private theorem prime_fiftyThreeAY_1088987 : Nat.Prime 1088987 := by norm_num
private theorem prime_fiftyThreeAY_1170011 : Nat.Prime 1170011 := by norm_num
private theorem prime_fiftyThreeAY_1177433 : Nat.Prime 1177433 := by norm_num
private theorem prime_fiftyThreeAY_1214683 : Nat.Prime 1214683 := by norm_num
private theorem prime_fiftyThreeAY_1244059 : Nat.Prime 1244059 := by norm_num
private theorem prime_fiftyThreeAY_1337969 : Nat.Prime 1337969 := by norm_num
private theorem prime_fiftyThreeAY_1338013 : Nat.Prime 1338013 := by norm_num
private theorem prime_fiftyThreeAY_1439701 : Nat.Prime 1439701 := by norm_num
private theorem prime_fiftyThreeAY_1452457 : Nat.Prime 1452457 := by norm_num
private theorem prime_fiftyThreeAY_1484281 : Nat.Prime 1484281 := by norm_num
private theorem prime_fiftyThreeAY_1618739 : Nat.Prime 1618739 := by norm_num
private theorem prime_fiftyThreeAY_1626503 : Nat.Prime 1626503 := by norm_num
private theorem prime_fiftyThreeAY_1643743 : Nat.Prime 1643743 := by norm_num
private theorem prime_fiftyThreeAY_1778453 : Nat.Prime 1778453 := by norm_num
private theorem prime_fiftyThreeAY_1931723 : Nat.Prime 1931723 := by norm_num
private theorem prime_fiftyThreeAY_2143019 : Nat.Prime 2143019 := by norm_num
private theorem prime_fiftyThreeAY_2190017 : Nat.Prime 2190017 := by norm_num
private theorem prime_fiftyThreeAY_2211161 : Nat.Prime 2211161 := by norm_num
private theorem prime_fiftyThreeAY_2263643 : Nat.Prime 2263643 := by norm_num
private theorem prime_fiftyThreeAY_2289773 : Nat.Prime 2289773 := by norm_num
private theorem prime_fiftyThreeAY_2295823 : Nat.Prime 2295823 := by norm_num
private theorem prime_fiftyThreeAY_2300527 : Nat.Prime 2300527 := by norm_num
private theorem prime_fiftyThreeAY_2326199 : Nat.Prime 2326199 := by norm_num
private theorem prime_fiftyThreeAY_2570801 : Nat.Prime 2570801 := by norm_num
private theorem prime_fiftyThreeAY_2604163 : Nat.Prime 2604163 := by norm_num
private theorem prime_fiftyThreeAY_2700851 : Nat.Prime 2700851 := by norm_num
private theorem prime_fiftyThreeAY_2837873 : Nat.Prime 2837873 := by norm_num
private theorem prime_fiftyThreeAY_2904211 : Nat.Prime 2904211 := by norm_num
private theorem prime_fiftyThreeAY_2971223 : Nat.Prime 2971223 := by norm_num
private theorem prime_fiftyThreeAY_3307489 : Nat.Prime 3307489 := by norm_num
private theorem prime_fiftyThreeAY_3358889 : Nat.Prime 3358889 := by norm_num
private theorem prime_fiftyThreeAY_3505651 : Nat.Prime 3505651 := by norm_num
private theorem prime_fiftyThreeAY_3973919 : Nat.Prime 3973919 := by norm_num
private theorem prime_fiftyThreeAY_4111199 : Nat.Prime 4111199 := by norm_num
private theorem prime_fiftyThreeAY_4244341 : Nat.Prime 4244341 := by norm_num
private theorem prime_fiftyThreeAY_4296997 : Nat.Prime 4296997 := by norm_num
private theorem prime_fiftyThreeAY_4677677 : Nat.Prime 4677677 := by norm_num
private theorem prime_fiftyThreeAY_4712479 : Nat.Prime 4712479 := by norm_num
private theorem prime_fiftyThreeAY_4929343 : Nat.Prime 4929343 := by norm_num
private theorem prime_fiftyThreeAY_5089829 : Nat.Prime 5089829 := by norm_num
private theorem prime_fiftyThreeAY_5293501 : Nat.Prime 5293501 := by norm_num
private theorem prime_fiftyThreeAY_5318581 : Nat.Prime 5318581 := by norm_num
private theorem prime_fiftyThreeAY_5903941 : Nat.Prime 5903941 := by norm_num
private theorem prime_fiftyThreeAY_6086893 : Nat.Prime 6086893 := by norm_num
private theorem prime_fiftyThreeAY_6438269 : Nat.Prime 6438269 := by norm_num
private theorem prime_fiftyThreeAY_6695903 : Nat.Prime 6695903 := by norm_num
private theorem prime_fiftyThreeAY_6858119 : Nat.Prime 6858119 := by norm_num
private theorem prime_fiftyThreeAY_7184851 : Nat.Prime 7184851 := by norm_num
private theorem prime_fiftyThreeAY_7186999 : Nat.Prime 7186999 := by norm_num
private theorem prime_fiftyThreeAY_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fiftyThreeAY_7846799 : Nat.Prime 7846799 := by norm_num
private theorem prime_fiftyThreeAY_8421929 : Nat.Prime 8421929 := by norm_num
private theorem prime_fiftyThreeAY_8851069 : Nat.Prime 8851069 := by norm_num
private theorem prime_fiftyThreeAY_9128923 : Nat.Prime 9128923 := by norm_num
private theorem prime_fiftyThreeAY_9671059 : Nat.Prime 9671059 := by norm_num
private theorem prime_fiftyThreeAY_9692993 : Nat.Prime 9692993 := by norm_num
private theorem prime_fiftyThreeAY_10488671 : Nat.Prime 10488671 := by norm_num
private theorem prime_fiftyThreeAY_11871157 : Nat.Prime 11871157 := by norm_num
private theorem prime_fiftyThreeAY_12741769 : Nat.Prime 12741769 := by norm_num
private theorem prime_fiftyThreeAY_12866681 : Nat.Prime 12866681 := by norm_num
private theorem prime_fiftyThreeAY_13490623 : Nat.Prime 13490623 := by norm_num
private theorem prime_fiftyThreeAY_13764431 : Nat.Prime 13764431 := by norm_num
private theorem prime_fiftyThreeAY_14301451 : Nat.Prime 14301451 := by norm_num
private theorem prime_fiftyThreeAY_14681141 : Nat.Prime 14681141 := by norm_num
private theorem prime_fiftyThreeAY_15807689 : Nat.Prime 15807689 := by norm_num
private theorem prime_fiftyThreeAY_15922177 : Nat.Prime 15922177 := by norm_num
private theorem prime_fiftyThreeAY_16504577 : Nat.Prime 16504577 := by norm_num
private theorem prime_fiftyThreeAY_16747649 : Nat.Prime 16747649 := by norm_num
private theorem prime_fiftyThreeAY_17330251 : Nat.Prime 17330251 := by norm_num
private theorem prime_fiftyThreeAY_18044717 : Nat.Prime 18044717 := by norm_num
private theorem prime_fiftyThreeAY_18175867 : Nat.Prime 18175867 := by norm_num
private theorem prime_fiftyThreeAY_19781833 : Nat.Prime 19781833 := by norm_num
private theorem prime_fiftyThreeAY_19831199 : Nat.Prime 19831199 := by norm_num
private theorem prime_fiftyThreeAY_20446511 : Nat.Prime 20446511 := by norm_num
private theorem prime_fiftyThreeAY_22728793 : Nat.Prime 22728793 := by norm_num
private theorem prime_fiftyThreeAY_26786083 : Nat.Prime 26786083 := by norm_num
private theorem prime_fiftyThreeAY_27255071 : Nat.Prime 27255071 := by norm_num
private theorem prime_fiftyThreeAY_28687271 : Nat.Prime 28687271 := by norm_num
private theorem prime_fiftyThreeAY_28798361 : Nat.Prime 28798361 := by norm_num
private theorem prime_fiftyThreeAY_29674363 : Nat.Prime 29674363 := by norm_num
private theorem prime_fiftyThreeAY_29940019 : Nat.Prime 29940019 := by norm_num
private theorem prime_fiftyThreeAY_31432243 : Nat.Prime 31432243 := by
  apply lucas_primality 31432243 (2 : ZMod 31432243)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1877, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1877, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_1877
      · exact prime_fiftyThreeAY_2791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31432243) ^ 15716121 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432243) ^ 10477414 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432243) ^ 16746 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432243) ^ 11262 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_31559093 : Nat.Prime 31559093 := by
  apply lucas_primality 31559093 (2 : ZMod 31559093)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (69821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (69821, 1)] : List FactorBlock).map factorBlockValue).prod) = 31559093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_113
      · exact prime_fiftyThreeAY_69821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31559093) ^ 15779546 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31559093) ^ 279284 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31559093) ^ 452 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_33495299 : Nat.Prime 33495299 := by
  apply lucas_primality 33495299 (2 : ZMod 33495299)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16747649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16747649, 1)] : List FactorBlock).map factorBlockValue).prod) = 33495299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_16747649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33495299) ^ 16747649 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 33495299) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_33816241 : Nat.Prime 33816241 := by
  apply lucas_primality 33816241 (11 : ZMod 33816241)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (67, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (67, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) = 33816241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_67
      · exact prime_fiftyThreeAY_701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33816241) ^ 16908120 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33816241) ^ 11272080 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33816241) ^ 6763248 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33816241) ^ 504720 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33816241) ^ 48240 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_33830977 : Nat.Prime 33830977 := by
  apply lucas_primality 33830977 (5 : ZMod 33830977)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (23, 1), (47, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (23, 1), (47, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 33830977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33830977) ^ 16915488 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33830977) ^ 11276992 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33830977) ^ 1470912 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33830977) ^ 719808 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33830977) ^ 207552 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_36127331 : Nat.Prime 36127331 := by
  apply lucas_primality 36127331 (2 : ZMod 36127331)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (124577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (124577, 1)] : List FactorBlock).map factorBlockValue).prod) = 36127331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_124577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36127331) ^ 18063665 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36127331) ^ 7225466 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36127331) ^ 1245770 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36127331) ^ 290 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_36832979 : Nat.Prime 36832979 := by
  apply lucas_primality 36832979 (2 : ZMod 36832979)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (439, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (439, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 36832979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_439
      · exact prime_fiftyThreeAY_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36832979) ^ 18416489 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36832979) ^ 5261854 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36832979) ^ 2833306 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36832979) ^ 83902 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36832979) ^ 79898 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_41381507 : Nat.Prime 41381507 := by
  apply lucas_primality 41381507 (2 : ZMod 41381507)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1088987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1088987, 1)] : List FactorBlock).map factorBlockValue).prod) = 41381507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_1088987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41381507) ^ 20690753 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41381507) ^ 2177974 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41381507) ^ 38 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_43208981 : Nat.Prime 43208981 := by
  apply lucas_primality 43208981 (2 : ZMod 43208981)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (47, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (47, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 43208981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43208981) ^ 21604490 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43208981) ^ 8641796 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43208981) ^ 1004860 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43208981) ^ 919340 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43208981) ^ 40420 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_49032149 : Nat.Prime 49032149 := by
  apply lucas_primality 49032149 (3 : ZMod 49032149)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (65551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (65551, 1)] : List FactorBlock).map factorBlockValue).prod) = 49032149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_65551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49032149) ^ 24516074 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 49032149) ^ 4457468 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 49032149) ^ 2884244 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 49032149) ^ 748 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_49429609 : Nat.Prime 49429609 := by
  apply lucas_primality 49429609 (7 : ZMod 49429609)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (121151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (121151, 1)] : List FactorBlock).map factorBlockValue).prod) = 49429609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_121151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 49429609) ^ 24714804 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 49429609) ^ 16476536 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 49429609) ^ 2907624 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 49429609) ^ 408 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_57374543 : Nat.Prime 57374543 := by
  apply lucas_primality 57374543 (5 : ZMod 57374543)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (28687271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (28687271, 1)] : List FactorBlock).map factorBlockValue).prod) = 57374543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_28687271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 57374543) ^ 28687271 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 57374543) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_57596723 : Nat.Prime 57596723 := by
  apply lucas_primality 57596723 (2 : ZMod 57596723)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (28798361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (28798361, 1)] : List FactorBlock).map factorBlockValue).prod) = 57596723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_28798361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 57596723) ^ 28798361 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 57596723) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_58879939 : Nat.Prime 58879939 := by
  apply lucas_primality 58879939 (2 : ZMod 58879939)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (58067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (58067, 1)] : List FactorBlock).map factorBlockValue).prod) = 58879939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_58067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58879939) ^ 29439969 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 58879939) ^ 19626646 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 58879939) ^ 4529226 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 58879939) ^ 1014 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_59726851 : Nat.Prime 59726851 := by
  apply lucas_primality 59726851 (2 : ZMod 59726851)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (307, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (307, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod) = 59726851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_307
      · exact prime_fiftyThreeAY_1297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59726851) ^ 29863425 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 59726851) ^ 19908950 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 59726851) ^ 11945370 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 59726851) ^ 194550 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 59726851) ^ 46050 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_61781003 : Nat.Prime 61781003 := by
  apply lucas_primality 61781003 (5 : ZMod 61781003)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (391019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (391019, 1)] : List FactorBlock).map factorBlockValue).prod) = 61781003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_79
      · exact prime_fiftyThreeAY_391019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 61781003) ^ 30890501 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 61781003) ^ 782038 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 61781003) ^ 158 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_62199083 : Nat.Prime 62199083 := by
  apply lucas_primality 62199083 (2 : ZMod 62199083)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (31, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (31, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod) = 62199083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_8291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62199083) ^ 31099541 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 62199083) ^ 5654462 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 62199083) ^ 2006422 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 62199083) ^ 7502 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_64419269 : Nat.Prime 64419269 := by
  apply lucas_primality 64419269 (2 : ZMod 64419269)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (89, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (89, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) = 64419269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_89
      · exact prime_fiftyThreeAY_3067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64419269) ^ 32209634 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64419269) ^ 1091852 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64419269) ^ 723812 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64419269) ^ 21004 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_64839493 : Nat.Prime 64839493 := by
  apply lucas_primality 64839493 (2 : ZMod 64839493)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (521, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (521, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) = 64839493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_521
      · exact prime_fiftyThreeAY_3457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64839493) ^ 32419746 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64839493) ^ 21613164 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64839493) ^ 124452 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64839493) ^ 18756 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_65609969 : Nat.Prime 65609969 := by
  apply lucas_primality 65609969 (3 : ZMod 65609969)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (601, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (601, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) = 65609969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_601
      · exact prime_fiftyThreeAY_6823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 65609969) ^ 32804984 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 65609969) ^ 109168 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 65609969) ^ 9616 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_71226943 : Nat.Prime 71226943 := by
  apply lucas_primality 71226943 (6 : ZMod 71226943)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11871157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11871157, 1)] : List FactorBlock).map factorBlockValue).prod) = 71226943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11871157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 71226943) ^ 35613471 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 71226943) ^ 23742314 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 71226943) ^ 6 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_72703469 : Nat.Prime 72703469 := by
  apply lucas_primality 72703469 (2 : ZMod 72703469)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18175867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18175867, 1)] : List FactorBlock).map factorBlockValue).prod) = 72703469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_18175867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72703469) ^ 36351734 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72703469) ^ 4 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_73509791 : Nat.Prime 73509791 := by
  apply lucas_primality 73509791 (11 : ZMod 73509791)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (170953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (170953, 1)] : List FactorBlock).map factorBlockValue).prod) = 73509791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_170953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 73509791) ^ 36754895 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 73509791) ^ 14701958 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 73509791) ^ 1709530 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 73509791) ^ 430 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_74001583 : Nat.Prime 74001583 := by
  apply lucas_primality 74001583 (3 : ZMod 74001583)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4111199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4111199, 1)] : List FactorBlock).map factorBlockValue).prod) = 74001583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_4111199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 74001583) ^ 37000791 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 74001583) ^ 24667194 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 74001583) ^ 18 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_74036827 : Nat.Prime 74036827 := by
  apply lucas_primality 74036827 (2 : ZMod 74036827)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (141833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (141833, 1)] : List FactorBlock).map factorBlockValue).prod) = 74036827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_141833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74036827) ^ 37018413 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 74036827) ^ 24678942 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 74036827) ^ 2552994 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 74036827) ^ 522 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_79462049 : Nat.Prime 79462049 := by
  apply lucas_primality 79462049 (3 : ZMod 79462049)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (89, 1), (27901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (89, 1), (27901, 1)] : List FactorBlock).map factorBlockValue).prod) = 79462049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_89
      · exact prime_fiftyThreeAY_27901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 79462049) ^ 39731024 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 79462049) ^ 892832 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 79462049) ^ 2848 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_83887753 : Nat.Prime 83887753 := by
  apply lucas_primality 83887753 (14 : ZMod 83887753)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (67, 1), (4013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (67, 1), (4013, 1)] : List FactorBlock).map factorBlockValue).prod) = 83887753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_67
      · exact prime_fiftyThreeAY_4013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 83887753) ^ 41943876 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (14 : ZMod 83887753) ^ 27962584 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (14 : ZMod 83887753) ^ 6452904 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (14 : ZMod 83887753) ^ 1252056 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (14 : ZMod 83887753) ^ 20904 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_84487607 : Nat.Prime 84487607 := by
  apply lucas_primality 84487607 (5 : ZMod 84487607)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1009, 1), (5981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1009, 1), (5981, 1)] : List FactorBlock).map factorBlockValue).prod) = 84487607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_1009
      · exact prime_fiftyThreeAY_5981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 84487607) ^ 42243803 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84487607) ^ 12069658 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84487607) ^ 83734 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84487607) ^ 14126 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_86458279 : Nat.Prime 86458279 := by
  apply lucas_primality 86458279 (3 : ZMod 86458279)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (139, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (139, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) = 86458279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_83
      · exact prime_fiftyThreeAY_139
      · exact prime_fiftyThreeAY_1249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 86458279) ^ 43229139 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 86458279) ^ 28819426 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 86458279) ^ 1041666 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 86458279) ^ 622002 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 86458279) ^ 69222 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_89277887 : Nat.Prime 89277887 := by
  apply lucas_primality 89277887 (5 : ZMod 89277887)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2239, 1), (19937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2239, 1), (19937, 1)] : List FactorBlock).map factorBlockValue).prod) = 89277887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_2239
      · exact prime_fiftyThreeAY_19937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 89277887) ^ 44638943 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 89277887) ^ 39874 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 89277887) ^ 4478 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_105291073 : Nat.Prime 105291073 := by
  apply lucas_primality 105291073 (5 : ZMod 105291073)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (53, 1), (3449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (53, 1), (3449, 1)] : List FactorBlock).map factorBlockValue).prod) = 105291073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_3449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 105291073) ^ 52645536 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 105291073) ^ 35097024 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 105291073) ^ 1986624 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 105291073) ^ 30528 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_107144333 : Nat.Prime 107144333 := by
  apply lucas_primality 107144333 (2 : ZMod 107144333)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26786083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26786083, 1)] : List FactorBlock).map factorBlockValue).prod) = 107144333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_26786083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 107144333) ^ 53572166 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 107144333) ^ 4 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_110001191 : Nat.Prime 110001191 := by
  apply lucas_primality 110001191 (11 : ZMod 110001191)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (359, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (359, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) = 110001191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_359
      · exact prime_fiftyThreeAY_2357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 110001191) ^ 55000595 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 110001191) ^ 22000238 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 110001191) ^ 8461630 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 110001191) ^ 306410 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 110001191) ^ 46670 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_129040553 : Nat.Prime 129040553 := by
  apply lucas_primality 129040553 (3 : ZMod 129040553)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (59, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (59, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 129040553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 129040553) ^ 64520276 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 129040553) ^ 6791608 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 129040553) ^ 2187128 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 129040553) ^ 8968 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_138659057 : Nat.Prime 138659057 := by
  apply lucas_primality 138659057 (3 : ZMod 138659057)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1123, 1), (7717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1123, 1), (7717, 1)] : List FactorBlock).map factorBlockValue).prod) = 138659057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1123
      · exact prime_fiftyThreeAY_7717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 138659057) ^ 69329528 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 138659057) ^ 123472 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 138659057) ^ 17968 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_139701949 : Nat.Prime 139701949 := by
  apply lucas_primality 139701949 (2 : ZMod 139701949)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (140263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (140263, 1)] : List FactorBlock).map factorBlockValue).prod) = 139701949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_83
      · exact prime_fiftyThreeAY_140263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139701949) ^ 69850974 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 139701949) ^ 46567316 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 139701949) ^ 1683156 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 139701949) ^ 996 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_147081271 : Nat.Prime 147081271 := by
  apply lucas_primality 147081271 (3 : ZMod 147081271)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (700387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (700387, 1)] : List FactorBlock).map factorBlockValue).prod) = 147081271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_700387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 147081271) ^ 73540635 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 147081271) ^ 49027090 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 147081271) ^ 29416254 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 147081271) ^ 21011610 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 147081271) ^ 210 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_163850273 : Nat.Prime 163850273 := by
  apply lucas_primality 163850273 (3 : ZMod 163850273)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (47, 1), (108943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (47, 1), (108943, 1)] : List FactorBlock).map factorBlockValue).prod) = 163850273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_108943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 163850273) ^ 81925136 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 163850273) ^ 3486176 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 163850273) ^ 1504 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_179771951 : Nat.Prime 179771951 := by
  apply lucas_primality 179771951 (7 : ZMod 179771951)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (419, 1), (8581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (419, 1), (8581, 1)] : List FactorBlock).map factorBlockValue).prod) = 179771951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_419
      · exact prime_fiftyThreeAY_8581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 179771951) ^ 89885975 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 179771951) ^ 35954390 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 179771951) ^ 429050 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 179771951) ^ 20950 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_191121449 : Nat.Prime 191121449 := by
  apply lucas_primality 191121449 (3 : ZMod 191121449)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (89, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (89, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) = 191121449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_89
      · exact prime_fiftyThreeAY_1237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191121449) ^ 95560724 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191121449) ^ 27303064 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191121449) ^ 6165208 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191121449) ^ 2147432 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191121449) ^ 154504 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_193622329 : Nat.Prime 193622329 := by
  apply lucas_primality 193622329 (7 : ZMod 193622329)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (29, 1), (47, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (29, 1), (47, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 193622329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_1973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 193622329) ^ 96811164 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 193622329) ^ 64540776 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 193622329) ^ 6676632 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 193622329) ^ 4119624 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 193622329) ^ 98136 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_211351817 : Nat.Prime 211351817 := by
  apply lucas_primality 211351817 (3 : ZMod 211351817)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (271, 1), (7499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (271, 1), (7499, 1)] : List FactorBlock).map factorBlockValue).prod) = 211351817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_271
      · exact prime_fiftyThreeAY_7499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 211351817) ^ 105675908 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 211351817) ^ 16257832 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 211351817) ^ 779896 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 211351817) ^ 28184 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_236868169 : Nat.Prime 236868169 := by
  apply lucas_primality 236868169 (7 : ZMod 236868169)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (429109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (429109, 1)] : List FactorBlock).map factorBlockValue).prod) = 236868169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_429109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 236868169) ^ 118434084 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 236868169) ^ 78956056 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 236868169) ^ 10298616 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 236868169) ^ 552 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_263488741 : Nat.Prime 263488741 := by
  apply lucas_primality 263488741 (2 : ZMod 263488741)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1061, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1061, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod) = 263488741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_1061
      · exact prime_fiftyThreeAY_4139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 263488741) ^ 131744370 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 263488741) ^ 87829580 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 263488741) ^ 52697748 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 263488741) ^ 248340 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 263488741) ^ 63660 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_316153781 : Nat.Prime 316153781 := by
  apply lucas_primality 316153781 (2 : ZMod 316153781)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (15807689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (15807689, 1)] : List FactorBlock).map factorBlockValue).prod) = 316153781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_15807689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 316153781) ^ 158076890 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 316153781) ^ 63230756 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 316153781) ^ 20 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_324636079 : Nat.Prime 324636079 := by
  apply lucas_primality 324636079 (3 : ZMod 324636079)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (131, 1), (31771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (131, 1), (31771, 1)] : List FactorBlock).map factorBlockValue).prod) = 324636079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_131
      · exact prime_fiftyThreeAY_31771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 324636079) ^ 162318039 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 324636079) ^ 108212026 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 324636079) ^ 24972006 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 324636079) ^ 2478138 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 324636079) ^ 10218 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_326926867 : Nat.Prime 326926867 := by
  apply lucas_primality 326926867 (3 : ZMod 326926867)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (189853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (189853, 1)] : List FactorBlock).map factorBlockValue).prod) = 326926867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_189853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 326926867) ^ 163463433 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 326926867) ^ 108975622 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 326926867) ^ 46703838 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 326926867) ^ 7973826 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 326926867) ^ 1722 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_330027079 : Nat.Prime 330027079 := by
  apply lucas_primality 330027079 (3 : ZMod 330027079)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (163, 1), (6367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (163, 1), (6367, 1)] : List FactorBlock).map factorBlockValue).prod) = 330027079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_163
      · exact prime_fiftyThreeAY_6367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 330027079) ^ 165013539 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 330027079) ^ 110009026 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 330027079) ^ 6226926 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 330027079) ^ 2024706 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 330027079) ^ 51834 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_353811541 : Nat.Prime 353811541 := by
  apply lucas_primality 353811541 (6 : ZMod 353811541)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (310361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (310361, 1)] : List FactorBlock).map factorBlockValue).prod) = 353811541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_310361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 353811541) ^ 176905770 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 353811541) ^ 117937180 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 353811541) ^ 70762308 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 353811541) ^ 18621660 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 353811541) ^ 1140 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_359543903 : Nat.Prime 359543903 := by
  apply lucas_primality 359543903 (5 : ZMod 359543903)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179771951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179771951, 1)] : List FactorBlock).map factorBlockValue).prod) = 359543903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_179771951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 359543903) ^ 179771951 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 359543903) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_374999473 : Nat.Prime 374999473 := by
  apply lucas_primality 374999473 (23 : ZMod 374999473)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (2604163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (2604163, 1)] : List FactorBlock).map factorBlockValue).prod) = 374999473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_2604163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 374999473) ^ 187499736 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (23 : ZMod 374999473) ^ 124999824 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (23 : ZMod 374999473) ^ 144 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_405407447 : Nat.Prime 405407447 := by
  apply lucas_primality 405407447 (5 : ZMod 405407447)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (37, 2), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (37, 2), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) = 405407447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_7793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 405407447) ^ 202703723 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 405407447) ^ 21337234 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 405407447) ^ 10956958 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 405407447) ^ 52022 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_415798379 : Nat.Prime 415798379 := by
  apply lucas_primality 415798379 (2 : ZMod 415798379)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (47, 1), (119551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (47, 1), (119551, 1)] : List FactorBlock).map factorBlockValue).prod) = 415798379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_119551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 415798379) ^ 207899189 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 415798379) ^ 11237794 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 415798379) ^ 8846774 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 415798379) ^ 3478 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_449044417 : Nat.Prime 449044417 := by
  apply lucas_primality 449044417 (5 : ZMod 449044417)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (779591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (779591, 1)] : List FactorBlock).map factorBlockValue).prod) = 449044417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_779591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 449044417) ^ 224522208 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 449044417) ^ 149681472 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 449044417) ^ 576 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_494916431 : Nat.Prime 494916431 := by
  apply lucas_primality 494916431 (7 : ZMod 494916431)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (383, 1), (129221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (383, 1), (129221, 1)] : List FactorBlock).map factorBlockValue).prod) = 494916431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_383
      · exact prime_fiftyThreeAY_129221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 494916431) ^ 247458215 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 494916431) ^ 98983286 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 494916431) ^ 1292210 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 494916431) ^ 3830 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_496876727 : Nat.Prime 496876727 := by
  apply lucas_primality 496876727 (5 : ZMod 496876727)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (1177433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (1177433, 1)] : List FactorBlock).map factorBlockValue).prod) = 496876727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_211
      · exact prime_fiftyThreeAY_1177433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 496876727) ^ 248438363 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 496876727) ^ 2354866 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 496876727) ^ 422 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_501145283 : Nat.Prime 501145283 := by
  apply lucas_primality 501145283 (2 : ZMod 501145283)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (113, 1), (199, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (113, 1), (199, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 501145283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_113
      · exact prime_fiftyThreeAY_199
      · exact prime_fiftyThreeAY_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 501145283) ^ 250572641 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 501145283) ^ 45558662 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 501145283) ^ 4434914 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 501145283) ^ 2518318 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 501145283) ^ 494714 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_502245923 : Nat.Prime 502245923 := by
  apply lucas_primality 502245923 (2 : ZMod 502245923)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (149, 1), (16363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (149, 1), (16363, 1)] : List FactorBlock).map factorBlockValue).prod) = 502245923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_103
      · exact prime_fiftyThreeAY_149
      · exact prime_fiftyThreeAY_16363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 502245923) ^ 251122961 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 502245923) ^ 4876174 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 502245923) ^ 3370778 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 502245923) ^ 30694 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_545491033 : Nat.Prime 545491033 := by
  apply lucas_primality 545491033 (7 : ZMod 545491033)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (22728793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (22728793, 1)] : List FactorBlock).map factorBlockValue).prod) = 545491033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_22728793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 545491033) ^ 272745516 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545491033) ^ 181830344 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545491033) ^ 24 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_672269347 : Nat.Prime 672269347 := by
  apply lucas_primality 672269347 (3 : ZMod 672269347)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (229, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (229, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 672269347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_229
      · exact prime_fiftyThreeAY_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 672269347) ^ 336134673 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 672269347) ^ 224089782 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 672269347) ^ 96038478 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 672269347) ^ 29229102 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 672269347) ^ 2935674 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 672269347) ^ 663642 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_685875871 : Nat.Prime 685875871 := by
  apply lucas_primality 685875871 (3 : ZMod 685875871)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (19, 1), (23, 1), (5813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (19, 1), (23, 1), (5813, 1)] : List FactorBlock).map factorBlockValue).prod) = 685875871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_5813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 685875871) ^ 342937935 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 685875871) ^ 228625290 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 685875871) ^ 137175174 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 685875871) ^ 36098730 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 685875871) ^ 29820690 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 685875871) ^ 117990 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_688494517 : Nat.Prime 688494517 := by
  apply lucas_primality 688494517 (2 : ZMod 688494517)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (57374543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (57374543, 1)] : List FactorBlock).map factorBlockValue).prod) = 688494517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_57374543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 688494517) ^ 344247258 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 688494517) ^ 229498172 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 688494517) ^ 12 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_713697529 : Nat.Prime 713697529 := by
  apply lucas_primality 713697529 (7 : ZMod 713697529)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2281, 1), (13037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2281, 1), (13037, 1)] : List FactorBlock).map factorBlockValue).prod) = 713697529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_2281
      · exact prime_fiftyThreeAY_13037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 713697529) ^ 356848764 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 713697529) ^ 237899176 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 713697529) ^ 312888 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 713697529) ^ 54744 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_884157161 : Nat.Prime 884157161 := by
  apply lucas_primality 884157161 (3 : ZMod 884157161)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (683, 1), (32363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (683, 1), (32363, 1)] : List FactorBlock).map factorBlockValue).prod) = 884157161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_683
      · exact prime_fiftyThreeAY_32363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 884157161) ^ 442078580 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 884157161) ^ 176831432 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 884157161) ^ 1294520 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 884157161) ^ 27320 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_987559273 : Nat.Prime 987559273 := by
  apply lucas_primality 987559273 (5 : ZMod 987559273)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (29, 1), (67567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (29, 1), (67567, 1)] : List FactorBlock).map factorBlockValue).prod) = 987559273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_67567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 987559273) ^ 493779636 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 987559273) ^ 329186424 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 987559273) ^ 141079896 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 987559273) ^ 34053768 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 987559273) ^ 14616 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_989832863 : Nat.Prime 989832863 := by
  apply lucas_primality 989832863 (5 : ZMod 989832863)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (494916431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (494916431, 1)] : List FactorBlock).map factorBlockValue).prod) = 989832863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_494916431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 989832863) ^ 494916431 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 989832863) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1002290567 : Nat.Prime 1002290567 := by
  apply lucas_primality 1002290567 (5 : ZMod 1002290567)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (501145283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (501145283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1002290567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_501145283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1002290567) ^ 501145283 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1002290567) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1004491847 : Nat.Prime 1004491847 := by
  apply lucas_primality 1004491847 (5 : ZMod 1004491847)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (502245923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (502245923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1004491847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_502245923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1004491847) ^ 502245923 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1004491847) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1083819931 : Nat.Prime 1083819931 := by
  apply lucas_primality 1083819931 (2 : ZMod 1083819931)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (36127331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (36127331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1083819931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_36127331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1083819931) ^ 541909965 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083819931) ^ 361273310 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083819931) ^ 216763986 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083819931) ^ 30 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1149917837 : Nat.Prime 1149917837 := by
  apply lucas_primality 1149917837 (2 : ZMod 1149917837)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (379, 1), (758521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (379, 1), (758521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1149917837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_379
      · exact prime_fiftyThreeAY_758521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1149917837) ^ 574958918 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149917837) ^ 3034084 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149917837) ^ 1516 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1380943121 : Nat.Prime 1380943121 := by
  apply lucas_primality 1380943121 (6 : ZMod 1380943121)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (181, 1), (95369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (181, 1), (95369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380943121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_181
      · exact prime_fiftyThreeAY_95369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1380943121) ^ 690471560 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1380943121) ^ 276188624 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1380943121) ^ 7629520 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1380943121) ^ 14480 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1628034827 : Nat.Prime 1628034827 := by
  apply lucas_primality 1628034827 (2 : ZMod 1628034827)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (74001583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (74001583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1628034827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_74001583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1628034827) ^ 814017413 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1628034827) ^ 148003166 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1628034827) ^ 22 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1730316121 : Nat.Prime 1730316121 := by
  apply lucas_primality 1730316121 (11 : ZMod 1730316121)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (131, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (131, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1730316121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_131
      · exact prime_fiftyThreeAY_8467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1730316121) ^ 865158060 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1730316121) ^ 576772040 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1730316121) ^ 346063224 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1730316121) ^ 133101240 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1730316121) ^ 13208520 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1730316121) ^ 204360 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2157263419 : Nat.Prime 2157263419 := by
  apply lucas_primality 2157263419 (3 : ZMod 2157263419)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359543903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359543903, 1)] : List FactorBlock).map factorBlockValue).prod) = 2157263419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_359543903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2157263419) ^ 1078631709 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2157263419) ^ 719087806 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2157263419) ^ 6 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2194078213 : Nat.Prime 2194078213 := by
  apply lucas_primality 2194078213 (2 : ZMod 2194078213)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (67, 1), (303217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (67, 1), (303217, 1)] : List FactorBlock).map factorBlockValue).prod) = 2194078213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_67
      · exact prime_fiftyThreeAY_303217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2194078213) ^ 1097039106 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2194078213) ^ 731359404 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2194078213) ^ 32747436 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2194078213) ^ 7236 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2677973629 : Nat.Prime 2677973629 := by
  apply lucas_primality 2677973629 (2 : ZMod 2677973629)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (38351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (38351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2677973629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_38351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2677973629) ^ 1338986814 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677973629) ^ 892657876 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677973629) ^ 243452148 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677973629) ^ 116433636 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677973629) ^ 69828 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2833865591 : Nat.Prime 2833865591 := by
  apply lucas_primality 2833865591 (7 : ZMod 2833865591)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1151, 1), (246209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1151, 1), (246209, 1)] : List FactorBlock).map factorBlockValue).prod) = 2833865591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_1151
      · exact prime_fiftyThreeAY_246209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2833865591) ^ 1416932795 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2833865591) ^ 566773118 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2833865591) ^ 2462090 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2833865591) ^ 11510 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2905653341 : Nat.Prime 2905653341 := by
  apply lucas_primality 2905653341 (2 : ZMod 2905653341)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1361, 1), (106747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1361, 1), (106747, 1)] : List FactorBlock).map factorBlockValue).prod) = 2905653341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_1361
      · exact prime_fiftyThreeAY_106747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2905653341) ^ 1452826670 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2905653341) ^ 581130668 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2905653341) ^ 2134940 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2905653341) ^ 27220 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2920097933 : Nat.Prime 2920097933 := by
  apply lucas_primality 2920097933 (2 : ZMod 2920097933)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (601, 1), (1214683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (601, 1), (1214683, 1)] : List FactorBlock).map factorBlockValue).prod) = 2920097933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_601
      · exact prime_fiftyThreeAY_1214683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2920097933) ^ 1460048966 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2920097933) ^ 4858732 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2920097933) ^ 2404 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3211212163 : Nat.Prime 3211212163 := by
  apply lucas_primality 3211212163 (2 : ZMod 3211212163)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2063, 1), (259429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2063, 1), (259429, 1)] : List FactorBlock).map factorBlockValue).prod) = 3211212163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_2063
      · exact prime_fiftyThreeAY_259429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3211212163) ^ 1605606081 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3211212163) ^ 1070404054 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3211212163) ^ 1556574 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3211212163) ^ 12378 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3308159147 : Nat.Prime 3308159147 := by
  apply lucas_primality 3308159147 (2 : ZMod 3308159147)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (677, 1), (41411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (677, 1), (41411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3308159147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_677
      · exact prime_fiftyThreeAY_41411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3308159147) ^ 1654079573 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3308159147) ^ 56070494 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3308159147) ^ 4886498 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3308159147) ^ 79886 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3846753593 : Nat.Prime 3846753593 := by
  apply lucas_primality 3846753593 (3 : ZMod 3846753593)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (3973919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (3973919, 1)] : List FactorBlock).map factorBlockValue).prod) = 3846753593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_3973919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3846753593) ^ 1923376796 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3846753593) ^ 349704872 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3846753593) ^ 968 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3975226253 : Nat.Prime 3975226253 := by
  apply lucas_primality 3975226253 (2 : ZMod 3975226253)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (43208981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (43208981, 1)] : List FactorBlock).map factorBlockValue).prod) = 3975226253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_43208981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3975226253) ^ 1987613126 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3975226253) ^ 172835924 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3975226253) ^ 92 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4621968433 : Nat.Prime 4621968433 := by
  apply lucas_primality 4621968433 (10 : ZMod 4621968433)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (17, 1), (59, 1), (10667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (17, 1), (59, 1), (10667, 1)] : List FactorBlock).map factorBlockValue).prod) = 4621968433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_10667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4621968433) ^ 2310984216 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 4621968433) ^ 1540656144 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 4621968433) ^ 271880496 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 4621968433) ^ 78338448 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 4621968433) ^ 433296 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4639287179 : Nat.Prime 4639287179 := by
  apply lucas_primality 4639287179 (2 : ZMod 4639287179)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3617, 1), (641317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3617, 1), (641317, 1)] : List FactorBlock).map factorBlockValue).prod) = 4639287179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3617
      · exact prime_fiftyThreeAY_641317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4639287179) ^ 2319643589 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4639287179) ^ 1282634 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4639287179) ^ 7234 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_5084725753 : Nat.Prime 5084725753 := by
  apply lucas_primality 5084725753 (5 : ZMod 5084725753)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (7846799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (7846799, 1)] : List FactorBlock).map factorBlockValue).prod) = 5084725753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7846799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5084725753) ^ 2542362876 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 5084725753) ^ 1694908584 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 5084725753) ^ 648 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_5110893259 : Nat.Prime 5110893259 := by
  apply lucas_primality 5110893259 (2 : ZMod 5110893259)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (127, 1), (353011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (127, 1), (353011, 1)] : List FactorBlock).map factorBlockValue).prod) = 5110893259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_127
      · exact prime_fiftyThreeAY_353011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5110893259) ^ 2555446629 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110893259) ^ 1703631086 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110893259) ^ 268994382 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110893259) ^ 40243254 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110893259) ^ 14478 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6066352147 : Nat.Prime 6066352147 := by
  apply lucas_primality 6066352147 (11 : ZMod 6066352147)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (5293501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (5293501, 1)] : List FactorBlock).map factorBlockValue).prod) = 6066352147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_191
      · exact prime_fiftyThreeAY_5293501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6066352147) ^ 3033176073 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 6066352147) ^ 2022117382 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 6066352147) ^ 31761006 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 6066352147) ^ 1146 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6953363107 : Nat.Prime 6953363107 := by
  apply lucas_primality 6953363107 (3 : ZMod 6953363107)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5227, 1), (221713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5227, 1), (221713, 1)] : List FactorBlock).map factorBlockValue).prod) = 6953363107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5227
      · exact prime_fiftyThreeAY_221713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6953363107) ^ 3476681553 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6953363107) ^ 2317787702 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6953363107) ^ 1330278 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6953363107) ^ 31362 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6962728511 : Nat.Prime 6962728511 := by
  apply lucas_primality 6962728511 (7 : ZMod 6962728511)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (16273, 1), (42787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (16273, 1), (42787, 1)] : List FactorBlock).map factorBlockValue).prod) = 6962728511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_16273
      · exact prime_fiftyThreeAY_42787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6962728511) ^ 3481364255 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6962728511) ^ 1392545702 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6962728511) ^ 427870 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6962728511) ^ 162730 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_7920649897 : Nat.Prime 7920649897 := by
  apply lucas_primality 7920649897 (7 : ZMod 7920649897)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (330027079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (330027079, 1)] : List FactorBlock).map factorBlockValue).prod) = 7920649897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_330027079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 7920649897) ^ 3960324948 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 7920649897) ^ 2640216632 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 7920649897) ^ 24 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9685779413 : Nat.Prime 9685779413 := by
  apply lucas_primality 9685779413 (2 : ZMod 9685779413)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (43, 2), (97, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (43, 2), (97, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 9685779413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_97
      · exact prime_fiftyThreeAY_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9685779413) ^ 4842889706 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9685779413) ^ 421120844 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9685779413) ^ 225250684 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9685779413) ^ 99853396 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9685779413) ^ 16500476 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_10047165721 : Nat.Prime 10047165721 := by
  apply lucas_primality 10047165721 (23 : ZMod 10047165721)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (2700851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (2700851, 1)] : List FactorBlock).map factorBlockValue).prod) = 10047165721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_2700851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 10047165721) ^ 5023582860 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (23 : ZMod 10047165721) ^ 3349055240 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (23 : ZMod 10047165721) ^ 2009433144 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (23 : ZMod 10047165721) ^ 324102120 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (23 : ZMod 10047165721) ^ 3720 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_11047544969 : Nat.Prime 11047544969 := by
  apply lucas_primality 11047544969 (3 : ZMod 11047544969)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1380943121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1380943121, 1)] : List FactorBlock).map factorBlockValue).prod) = 11047544969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1380943121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11047544969) ^ 5523772484 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11047544969) ^ 8 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_11998410521 : Nat.Prime 11998410521 := by
  apply lucas_primality 11998410521 (3 : ZMod 11998410521)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (131, 1), (2289773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (131, 1), (2289773, 1)] : List FactorBlock).map factorBlockValue).prod) = 11998410521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_131
      · exact prime_fiftyThreeAY_2289773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11998410521) ^ 5999205260 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998410521) ^ 2399682104 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998410521) ^ 91590920 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998410521) ^ 5240 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_12000802727 : Nat.Prime 12000802727 := by
  apply lucas_primality 12000802727 (5 : ZMod 12000802727)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (545491033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (545491033, 1)] : List FactorBlock).map factorBlockValue).prod) = 12000802727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_545491033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12000802727) ^ 6000401363 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 12000802727) ^ 1090982066 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 12000802727) ^ 22 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_12487271039 : Nat.Prime 12487271039 := by
  apply lucas_primality 12487271039 (11 : ZMod 12487271039)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (79, 1), (7184851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (79, 1), (7184851, 1)] : List FactorBlock).map factorBlockValue).prod) = 12487271039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_79
      · exact prime_fiftyThreeAY_7184851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12487271039) ^ 6243635519 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 12487271039) ^ 1135206458 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 12487271039) ^ 158066722 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 12487271039) ^ 1738 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_18823541717 : Nat.Prime 18823541717 := by
  apply lucas_primality 18823541717 (2 : ZMod 18823541717)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (672269347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (672269347, 1)] : List FactorBlock).map factorBlockValue).prod) = 18823541717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_672269347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18823541717) ^ 9411770858 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18823541717) ^ 2689077388 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18823541717) ^ 28 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_19423189859 : Nat.Prime 19423189859 := by
  apply lucas_primality 19423189859 (2 : ZMod 19423189859)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (236868169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (236868169, 1)] : List FactorBlock).map factorBlockValue).prod) = 19423189859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_236868169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19423189859) ^ 9711594929 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19423189859) ^ 473736338 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19423189859) ^ 82 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_19958322193 : Nat.Prime 19958322193 := by
  apply lucas_primality 19958322193 (5 : ZMod 19958322193)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (415798379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (415798379, 1)] : List FactorBlock).map factorBlockValue).prod) = 19958322193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_415798379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19958322193) ^ 9979161096 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 19958322193) ^ 6652774064 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 19958322193) ^ 48 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_20560266481 : Nat.Prime 20560266481 := by
  apply lucas_primality 20560266481 (7 : ZMod 20560266481)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (17, 1), (439, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (17, 1), (439, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 20560266481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_439
      · exact prime_fiftyThreeAY_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20560266481) ^ 10280133240 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20560266481) ^ 6853422160 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20560266481) ^ 4112053296 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20560266481) ^ 1581558960 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20560266481) ^ 1209427440 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20560266481) ^ 46834320 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20560266481) ^ 23284560 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_21428866601 : Nat.Prime 21428866601 := by
  apply lucas_primality 21428866601 (3 : ZMod 21428866601)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (107144333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (107144333, 1)] : List FactorBlock).map factorBlockValue).prod) = 21428866601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_107144333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21428866601) ^ 10714433300 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 21428866601) ^ 4285773320 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 21428866601) ^ 200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_25839616007 : Nat.Prime 25839616007 := by
  apply lucas_primality 25839616007 (5 : ZMod 25839616007)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2621, 1), (4929343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2621, 1), (4929343, 1)] : List FactorBlock).map factorBlockValue).prod) = 25839616007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_2621
      · exact prime_fiftyThreeAY_4929343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 25839616007) ^ 12919808003 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 25839616007) ^ 9858686 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 25839616007) ^ 5242 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_26588706317 : Nat.Prime 26588706317 := by
  apply lucas_primality 26588706317 (2 : ZMod 26588706317)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (3919, 1), (5869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (3919, 1), (5869, 1)] : List FactorBlock).map factorBlockValue).prod) = 26588706317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_3919
      · exact prime_fiftyThreeAY_5869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26588706317) ^ 13294353158 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26588706317) ^ 1564041548 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26588706317) ^ 6784564 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26588706317) ^ 4530364 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_27223118821 : Nat.Prime 27223118821 := by
  apply lucas_primality 27223118821 (7 : ZMod 27223118821)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (5101, 1), (9883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (5101, 1), (9883, 1)] : List FactorBlock).map factorBlockValue).prod) = 27223118821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_5101
      · exact prime_fiftyThreeAY_9883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27223118821) ^ 13611559410 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 27223118821) ^ 9074372940 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 27223118821) ^ 5444623764 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 27223118821) ^ 5336820 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 27223118821) ^ 2754540 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_27279921791 : Nat.Prime 27279921791 := by
  apply lucas_primality 27279921791 (11 : ZMod 27279921791)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (4391, 1), (56479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (4391, 1), (56479, 1)] : List FactorBlock).map factorBlockValue).prod) = 27279921791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_4391
      · exact prime_fiftyThreeAY_56479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 27279921791) ^ 13639960895 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 27279921791) ^ 5455984358 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 27279921791) ^ 2479992890 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 27279921791) ^ 6212690 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 27279921791) ^ 483010 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_31778147551 : Nat.Prime 31778147551 := by
  apply lucas_primality 31778147551 (6 : ZMod 31778147551)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (947, 1), (223711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (947, 1), (223711, 1)] : List FactorBlock).map factorBlockValue).prod) = 31778147551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_947
      · exact prime_fiftyThreeAY_223711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31778147551) ^ 15889073775 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31778147551) ^ 10592715850 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31778147551) ^ 6355629510 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31778147551) ^ 33556650 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31778147551) ^ 142050 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_33010811279 : Nat.Prime 33010811279 := by
  apply lucas_primality 33010811279 (17 : ZMod 33010811279)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (523, 1), (31559093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (523, 1), (31559093, 1)] : List FactorBlock).map factorBlockValue).prod) = 33010811279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_523
      · exact prime_fiftyThreeAY_31559093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 33010811279) ^ 16505405639 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 33010811279) ^ 63118186 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 33010811279) ^ 1046 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_53321907803 : Nat.Prime 53321907803 := by
  apply lucas_primality 53321907803 (2 : ZMod 53321907803)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (157, 1), (1153, 1), (4751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (157, 1), (1153, 1), (4751, 1)] : List FactorBlock).map factorBlockValue).prod) = 53321907803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_157
      · exact prime_fiftyThreeAY_1153
      · exact prime_fiftyThreeAY_4751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53321907803) ^ 26660953901 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53321907803) ^ 1720061542 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53321907803) ^ 339629986 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53321907803) ^ 46246234 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53321907803) ^ 11223302 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_53832921049 : Nat.Prime 53832921049 := by
  apply lucas_primality 53832921049 (7 : ZMod 53832921049)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (601, 1), (1244059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (601, 1), (1244059, 1)] : List FactorBlock).map factorBlockValue).prod) = 53832921049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_601
      · exact prime_fiftyThreeAY_1244059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 53832921049) ^ 26916460524 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 53832921049) ^ 17944307016 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 53832921049) ^ 89572248 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 53832921049) ^ 43272 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_55463621197 : Nat.Prime 55463621197 := by
  apply lucas_primality 55463621197 (6 : ZMod 55463621197)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4621968433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4621968433, 1)] : List FactorBlock).map factorBlockValue).prod) = 55463621197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_4621968433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 55463621197) ^ 27731810598 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 55463621197) ^ 18487873732 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 55463621197) ^ 12 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_56531462443 : Nat.Prime 56531462443 := by
  apply lucas_primality 56531462443 (2 : ZMod 56531462443)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (2879, 1), (35963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (2879, 1), (35963, 1)] : List FactorBlock).map factorBlockValue).prod) = 56531462443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_2879
      · exact prime_fiftyThreeAY_35963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56531462443) ^ 28265731221 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56531462443) ^ 18843820814 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56531462443) ^ 8075923206 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56531462443) ^ 4348574034 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56531462443) ^ 19635798 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56531462443) ^ 1571934 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_58114676479 : Nat.Prime 58114676479 := by
  apply lucas_primality 58114676479 (3 : ZMod 58114676479)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9685779413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9685779413, 1)] : List FactorBlock).map factorBlockValue).prod) = 58114676479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_9685779413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 58114676479) ^ 29057338239 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58114676479) ^ 19371558826 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58114676479) ^ 6 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_65443518011 : Nat.Prime 65443518011 := by
  apply lucas_primality 65443518011 (2 : ZMod 65443518011)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (37, 1), (379, 1), (35899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (37, 1), (379, 1), (35899, 1)] : List FactorBlock).map factorBlockValue).prod) = 65443518011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_379
      · exact prime_fiftyThreeAY_35899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65443518011) ^ 32721759005 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65443518011) ^ 13088703602 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65443518011) ^ 5034116770 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65443518011) ^ 1768743730 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65443518011) ^ 172674190 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65443518011) ^ 1822990 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_69186294907 : Nat.Prime 69186294907 := by
  apply lucas_primality 69186294907 (2 : ZMod 69186294907)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (64419269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (64419269, 1)] : List FactorBlock).map factorBlockValue).prod) = 69186294907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_179
      · exact prime_fiftyThreeAY_64419269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69186294907) ^ 34593147453 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 69186294907) ^ 23062098302 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 69186294907) ^ 386515614 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 69186294907) ^ 1074 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_75023851061 : Nat.Prime 75023851061 := by
  apply lucas_primality 75023851061 (3 : ZMod 75023851061)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (83, 1), (431, 1), (5519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (83, 1), (431, 1), (5519, 1)] : List FactorBlock).map factorBlockValue).prod) = 75023851061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_83
      · exact prime_fiftyThreeAY_431
      · exact prime_fiftyThreeAY_5519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75023851061) ^ 37511925530 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75023851061) ^ 15004770212 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75023851061) ^ 3948623740 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75023851061) ^ 903901820 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75023851061) ^ 174069260 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75023851061) ^ 13593740 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_84392572357 : Nat.Prime 84392572357 := by
  apply lucas_primality 84392572357 (5 : ZMod 84392572357)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (157, 1), (1061, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (157, 1), (1061, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) = 84392572357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_157
      · exact prime_fiftyThreeAY_1061
      · exact prime_fiftyThreeAY_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 84392572357) ^ 42196286178 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84392572357) ^ 28130857452 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84392572357) ^ 537532308 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84392572357) ^ 79540596 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 84392572357) ^ 17990316 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_96464774767 : Nat.Prime 96464774767 := by
  apply lucas_primality 96464774767 (3 : ZMod 96464774767)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (83, 1), (8421929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (83, 1), (8421929, 1)] : List FactorBlock).map factorBlockValue).prod) = 96464774767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_83
      · exact prime_fiftyThreeAY_8421929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96464774767) ^ 48232387383 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 96464774767) ^ 32154924922 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 96464774767) ^ 4194120642 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 96464774767) ^ 1162226202 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 96464774767) ^ 11454 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_103740820609 : Nat.Prime 103740820609 := by
  apply lucas_primality 103740820609 (7 : ZMod 103740820609)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (9689, 1), (27883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (9689, 1), (27883, 1)] : List FactorBlock).map factorBlockValue).prod) = 103740820609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_9689
      · exact prime_fiftyThreeAY_27883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 103740820609) ^ 51870410304 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 103740820609) ^ 34580273536 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 103740820609) ^ 10707072 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 103740820609) ^ 3720576 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_116066403989 : Nat.Prime 116066403989 := by
  apply lucas_primality 116066403989 (2 : ZMod 116066403989)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (283, 1), (3307489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (283, 1), (3307489, 1)] : List FactorBlock).map factorBlockValue).prod) = 116066403989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_283
      · exact prime_fiftyThreeAY_3307489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116066403989) ^ 58033201994 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 116066403989) ^ 3744077548 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 116066403989) ^ 410128636 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 116066403989) ^ 35092 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_130887036023 : Nat.Prime 130887036023 := by
  apply lucas_primality 130887036023 (5 : ZMod 130887036023)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65443518011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65443518011, 1)] : List FactorBlock).map factorBlockValue).prod) = 130887036023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_65443518011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 130887036023) ^ 65443518011 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 130887036023) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_148209875173 : Nat.Prime 148209875173 := by
  apply lucas_primality 148209875173 (5 : ZMod 148209875173)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (24623, 1), (55733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (24623, 1), (55733, 1)] : List FactorBlock).map factorBlockValue).prod) = 148209875173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_24623
      · exact prime_fiftyThreeAY_55733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 148209875173) ^ 74104937586 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 148209875173) ^ 49403291724 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 148209875173) ^ 6019164 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 148209875173) ^ 2659284 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_175584222977 : Nat.Prime 175584222977 := by
  apply lucas_primality 175584222977 (3 : ZMod 175584222977)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (685875871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (685875871, 1)] : List FactorBlock).map factorBlockValue).prod) = 175584222977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_685875871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 175584222977) ^ 87792111488 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 175584222977) ^ 256 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_214677037331 : Nat.Prime 214677037331 := by
  apply lucas_primality 214677037331 (6 : ZMod 214677037331)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (37, 1), (1033, 1), (80239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (37, 1), (1033, 1), (80239, 1)] : List FactorBlock).map factorBlockValue).prod) = 214677037331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_1033
      · exact prime_fiftyThreeAY_80239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 214677037331) ^ 107338518665 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 214677037331) ^ 42935407466 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 214677037331) ^ 30668148190 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 214677037331) ^ 5802082090 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 214677037331) ^ 207819010 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 214677037331) ^ 2675470 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_232458705917 : Nat.Prime 232458705917 := by
  apply lucas_primality 232458705917 (2 : ZMod 232458705917)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (58114676479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (58114676479, 1)] : List FactorBlock).map factorBlockValue).prod) = 232458705917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_58114676479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 232458705917) ^ 116229352958 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 232458705917) ^ 4 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_239657734697 : Nat.Prime 239657734697 := by
  apply lucas_primality 239657734697 (3 : ZMod 239657734697)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (4817, 1), (327319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (4817, 1), (327319, 1)] : List FactorBlock).map factorBlockValue).prod) = 239657734697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_4817
      · exact prime_fiftyThreeAY_327319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 239657734697) ^ 119828867348 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 239657734697) ^ 12613564984 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 239657734697) ^ 49752488 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 239657734697) ^ 732184 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_256528695077 : Nat.Prime 256528695077 := by
  apply lucas_primality 256528695077 (2 : ZMod 256528695077)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (6113, 1), (338423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (6113, 1), (338423, 1)] : List FactorBlock).map factorBlockValue).prod) = 256528695077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_6113
      · exact prime_fiftyThreeAY_338423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 256528695077) ^ 128264347538 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256528695077) ^ 8275119196 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256528695077) ^ 41964452 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256528695077) ^ 758012 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_322012213141 : Nat.Prime 322012213141 := by
  apply lucas_primality 322012213141 (6 : ZMod 322012213141)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (1019, 1), (86341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (1019, 1), (86341, 1)] : List FactorBlock).map factorBlockValue).prod) = 322012213141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_61
      · exact prime_fiftyThreeAY_1019
      · exact prime_fiftyThreeAY_86341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 322012213141) ^ 161006106570 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 322012213141) ^ 107337404380 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 322012213141) ^ 64402442628 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 322012213141) ^ 5278888740 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 322012213141) ^ 316008060 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 322012213141) ^ 3729540 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_352963042981 : Nat.Prime 352963042981 := by
  apply lucas_primality 352963042981 (2 : ZMod 352963042981)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (23, 1), (43, 2), (79, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (23, 1), (43, 2), (79, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 352963042981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_79
      · exact prime_fiftyThreeAY_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 352963042981) ^ 176481521490 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 117654347660 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 70592608596 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 20762531940 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 15346219260 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 8208442860 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 4467886620 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 352963042981) ^ 3426825660 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_361697965957 : Nat.Prime 361697965957 := by
  apply lucas_primality 361697965957 (2 : ZMod 361697965957)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10047165721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10047165721, 1)] : List FactorBlock).map factorBlockValue).prod) = 361697965957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_10047165721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 361697965957) ^ 180848982978 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 361697965957) ^ 120565988652 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 361697965957) ^ 36 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_393763550881 : Nat.Prime 393763550881 := by
  apply lucas_primality 393763550881 (22 : ZMod 393763550881)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (53, 1), (2211161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (53, 1), (2211161, 1)] : List FactorBlock).map factorBlockValue).prod) = 393763550881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_2211161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 393763550881) ^ 196881775440 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 393763550881) ^ 131254516960 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 393763550881) ^ 78752710176 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 393763550881) ^ 56251935840 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 393763550881) ^ 7429500960 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 393763550881) ^ 178080 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_529493203937 : Nat.Prime 529493203937 := by
  apply lucas_primality 529493203937 (3 : ZMod 529493203937)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (83, 1), (149, 1), (1337969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (83, 1), (149, 1), (1337969, 1)] : List FactorBlock).map factorBlockValue).prod) = 529493203937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_83
      · exact prime_fiftyThreeAY_149
      · exact prime_fiftyThreeAY_1337969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 529493203937) ^ 264746601968 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 529493203937) ^ 6379436192 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 529493203937) ^ 3553645664 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 529493203937) ^ 395744 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_546014967781 : Nat.Prime 546014967781 := by
  apply lucas_primality 546014967781 (6 : ZMod 546014967781)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (47, 1), (193622329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (47, 1), (193622329, 1)] : List FactorBlock).map factorBlockValue).prod) = 546014967781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_193622329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 546014967781) ^ 273007483890 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 546014967781) ^ 182004989260 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 546014967781) ^ 109202993556 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 546014967781) ^ 11617339740 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 546014967781) ^ 2820 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_547115925067 : Nat.Prime 547115925067 := by
  apply lucas_primality 547115925067 (2 : ZMod 547115925067)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1087, 1), (83887753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1087, 1), (83887753, 1)] : List FactorBlock).map factorBlockValue).prod) = 547115925067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_1087
      · exact prime_fiftyThreeAY_83887753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 547115925067) ^ 273557962533 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 547115925067) ^ 182371975022 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 547115925067) ^ 503326518 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 547115925067) ^ 6522 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_572006655919 : Nat.Prime 572006655919 := by
  apply lucas_primality 572006655919 (3 : ZMod 572006655919)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31778147551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31778147551, 1)] : List FactorBlock).map factorBlockValue).prod) = 572006655919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_31778147551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 572006655919) ^ 286003327959 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 572006655919) ^ 190668885306 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 572006655919) ^ 18 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_601540174199 : Nat.Prime 601540174199 := by
  apply lucas_primality 601540174199 (17 : ZMod 601540174199)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (2920097933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (2920097933, 1)] : List FactorBlock).map factorBlockValue).prod) = 601540174199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_103
      · exact prime_fiftyThreeAY_2920097933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 601540174199) ^ 300770087099 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 601540174199) ^ 5840195866 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 601540174199) ^ 206 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_621542075489 : Nat.Prime 621542075489 := by
  apply lucas_primality 621542075489 (3 : ZMod 621542075489)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19423189859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19423189859, 1)] : List FactorBlock).map factorBlockValue).prod) = 621542075489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19423189859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 621542075489) ^ 310771037744 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 621542075489) ^ 32 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_628241242891 : Nat.Prime 628241242891 := by
  apply lucas_primality 628241242891 (3 : ZMod 628241242891)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (619, 1), (33830977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (619, 1), (33830977, 1)] : List FactorBlock).map factorBlockValue).prod) = 628241242891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_619
      · exact prime_fiftyThreeAY_33830977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 628241242891) ^ 314120621445 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 628241242891) ^ 209413747630 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 628241242891) ^ 125648248578 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 628241242891) ^ 1014929310 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 628241242891) ^ 18570 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_696448237169 : Nat.Prime 696448237169 := by
  apply lucas_primality 696448237169 (3 : ZMod 696448237169)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (113, 1), (751, 1), (512921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (113, 1), (751, 1), (512921, 1)] : List FactorBlock).map factorBlockValue).prod) = 696448237169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_113
      · exact prime_fiftyThreeAY_751
      · exact prime_fiftyThreeAY_512921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 696448237169) ^ 348224118584 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 696448237169) ^ 6163258736 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 696448237169) ^ 927361168 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 696448237169) ^ 1357808 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1061252696579 : Nat.Prime 1061252696579 := by
  apply lucas_primality 1061252696579 (2 : ZMod 1061252696579)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (337, 1), (691, 1), (25603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (337, 1), (691, 1), (25603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1061252696579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_89
      · exact prime_fiftyThreeAY_337
      · exact prime_fiftyThreeAY_691
      · exact prime_fiftyThreeAY_25603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1061252696579) ^ 530626348289 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1061252696579) ^ 11924187602 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1061252696579) ^ 3149117794 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1061252696579) ^ 1535821558 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1061252696579) ^ 41450326 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1145384350889 : Nat.Prime 1145384350889 := by
  apply lucas_primality 1145384350889 (3 : ZMod 1145384350889)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (98573, 1), (1452457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (98573, 1), (1452457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1145384350889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_98573
      · exact prime_fiftyThreeAY_1452457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1145384350889) ^ 572692175444 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145384350889) ^ 11619656 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145384350889) ^ 788584 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1468605749659 : Nat.Prime 1468605749659 := by
  apply lucas_primality 1468605749659 (3 : ZMod 1468605749659)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (34057, 1), (7186999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (34057, 1), (7186999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1468605749659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_34057
      · exact prime_fiftyThreeAY_7186999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1468605749659) ^ 734302874829 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1468605749659) ^ 489535249886 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1468605749659) ^ 43121994 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1468605749659) ^ 204342 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1519066302427 : Nat.Prime 1519066302427 := by
  apply lucas_primality 1519066302427 (2 : ZMod 1519066302427)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (84392572357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (84392572357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1519066302427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_84392572357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1519066302427) ^ 759533151213 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1519066302427) ^ 506355434142 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1519066302427) ^ 18 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_35279
      · exact prime_fiftyThreeAY_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2260943641367 : Nat.Prime 2260943641367 := by
  apply lucas_primality 2260943641367 (5 : ZMod 2260943641367)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (547, 1), (3967, 1), (520967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (547, 1), (3967, 1), (520967, 1)] : List FactorBlock).map factorBlockValue).prod) = 2260943641367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_547
      · exact prime_fiftyThreeAY_3967
      · exact prime_fiftyThreeAY_520967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2260943641367) ^ 1130471820683 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2260943641367) ^ 4133352178 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2260943641367) ^ 569937898 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2260943641367) ^ 4339898 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2550604081537 : Nat.Prime 2550604081537 := by
  apply lucas_primality 2550604081537 (13 : ZMod 2550604081537)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 1), (17, 1), (23, 1), (53, 1), (15263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 1), (17, 1), (23, 1), (53, 1), (15263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2550604081537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_15263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2550604081537) ^ 1275302040768 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2550604081537) ^ 850201360512 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2550604081537) ^ 364372011648 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2550604081537) ^ 150035534208 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2550604081537) ^ 110895829632 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2550604081537) ^ 48124605312 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2550604081537) ^ 167110272 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2969641954159 : Nat.Prime 2969641954159 := by
  apply lucas_primality 2969641954159 (6 : ZMod 2969641954159)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (9619, 1), (4677677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (9619, 1), (4677677, 1)] : List FactorBlock).map factorBlockValue).prod) = 2969641954159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_9619
      · exact prime_fiftyThreeAY_4677677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2969641954159) ^ 1484820977079 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 2969641954159) ^ 989880651386 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 2969641954159) ^ 269967450378 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 2969641954159) ^ 308726682 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 2969641954159) ^ 634854 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3629507452427 : Nat.Prime 3629507452427 := by
  apply lucas_primality 3629507452427 (5 : ZMod 3629507452427)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (127, 1), (359, 1), (80737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (127, 1), (359, 1), (80737, 1)] : List FactorBlock).map factorBlockValue).prod) = 3629507452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_127
      · exact prime_fiftyThreeAY_359
      · exact prime_fiftyThreeAY_80737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3629507452427) ^ 1814753726213 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629507452427) ^ 213500438378 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629507452427) ^ 125155429394 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629507452427) ^ 28578798838 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629507452427) ^ 10110048614 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629507452427) ^ 44954698 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4705151111321 : Nat.Prime 4705151111321 := by
  apply lucas_primality 4705151111321 (7 : ZMod 4705151111321)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (523, 1), (20446511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (523, 1), (20446511, 1)] : List FactorBlock).map factorBlockValue).prod) = 4705151111321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_523
      · exact prime_fiftyThreeAY_20446511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4705151111321) ^ 2352575555660 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4705151111321) ^ 941030222264 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4705151111321) ^ 427741010120 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4705151111321) ^ 8996464840 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4705151111321) ^ 230120 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4915775686039 : Nat.Prime 4915775686039 := by
  apply lucas_primality 4915775686039 (3 : ZMod 4915775686039)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (135181, 1), (865819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (135181, 1), (865819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4915775686039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_135181
      · exact prime_fiftyThreeAY_865819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4915775686039) ^ 2457887843019 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4915775686039) ^ 1638591895346 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4915775686039) ^ 702253669434 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4915775686039) ^ 36364398 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4915775686039) ^ 5677602 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6263603297927 : Nat.Prime 6263603297927 := by
  apply lucas_primality 6263603297927 (5 : ZMod 6263603297927)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (13901, 1), (17330251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (13901, 1), (17330251, 1)] : List FactorBlock).map factorBlockValue).prod) = 6263603297927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_13901
      · exact prime_fiftyThreeAY_17330251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6263603297927) ^ 3131801648963 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6263603297927) ^ 481815638302 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6263603297927) ^ 450586526 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6263603297927) ^ 361426 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6365137880713 : Nat.Prime 6365137880713 := by
  apply lucas_primality 6365137880713 (5 : ZMod 6365137880713)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (17, 1), (29, 1), (41381507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (17, 1), (29, 1), (41381507, 1)] : List FactorBlock).map factorBlockValue).prod) = 6365137880713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_41381507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6365137880713) ^ 3182568940356 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6365137880713) ^ 2121712626904 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6365137880713) ^ 489625990824 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6365137880713) ^ 374419875336 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6365137880713) ^ 219487513128 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6365137880713) ^ 153816 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_7415017701979 : Nat.Prime 7415017701979 := by
  apply lucas_primality 7415017701979 (10 : ZMod 7415017701979)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (11998410521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (11998410521, 1)] : List FactorBlock).map factorBlockValue).prod) = 7415017701979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_103
      · exact prime_fiftyThreeAY_11998410521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 7415017701979) ^ 3707508850989 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7415017701979) ^ 2471672567326 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7415017701979) ^ 71990463126 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7415017701979) ^ 618 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_8079836041819 : Nat.Prime 8079836041819 := by
  apply lucas_primality 8079836041819 (2 : ZMod 8079836041819)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11743, 1), (12741769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11743, 1), (12741769, 1)] : List FactorBlock).map factorBlockValue).prod) = 8079836041819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11743
      · exact prime_fiftyThreeAY_12741769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8079836041819) ^ 4039918020909 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8079836041819) ^ 2693278680606 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8079836041819) ^ 688055526 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8079836041819) ^ 634122 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_8940773559919 : Nat.Prime 8940773559919 := by
  apply lucas_primality 8940773559919 (3 : ZMod 8940773559919)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (647, 1), (12866681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (647, 1), (12866681, 1)] : List FactorBlock).map factorBlockValue).prod) = 8940773559919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_179
      · exact prime_fiftyThreeAY_647
      · exact prime_fiftyThreeAY_12866681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8940773559919) ^ 4470386779959 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8940773559919) ^ 2980257853306 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8940773559919) ^ 49948455642 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8940773559919) ^ 13818815394 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8940773559919) ^ 694878 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9334971491081 : Nat.Prime 9334971491081 := by
  apply lucas_primality 9334971491081 (3 : ZMod 9334971491081)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17299, 1), (13490623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17299, 1), (13490623, 1)] : List FactorBlock).map factorBlockValue).prod) = 9334971491081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_17299
      · exact prime_fiftyThreeAY_13490623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9334971491081) ^ 4667485745540 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9334971491081) ^ 1866994298216 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9334971491081) ^ 539624920 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9334971491081) ^ 691960 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_21501034371689 : Nat.Prime 21501034371689 := by
  apply lucas_primality 21501034371689 (3 : ZMod 21501034371689)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (80239, 1), (33495299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (80239, 1), (33495299, 1)] : List FactorBlock).map factorBlockValue).prod) = 21501034371689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_80239
      · exact prime_fiftyThreeAY_33495299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21501034371689) ^ 10750517185844 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 21501034371689) ^ 267962392 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 21501034371689) ^ 641912 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_22286343589409 : Nat.Prime 22286343589409 := by
  apply lucas_primality 22286343589409 (3 : ZMod 22286343589409)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (696448237169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (696448237169, 1)] : List FactorBlock).map factorBlockValue).prod) = 22286343589409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_696448237169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 22286343589409) ^ 11143171794704 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22286343589409) ^ 32 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_25544593197239 : Nat.Prime 25544593197239 := by
  apply lucas_primality 25544593197239 (7 : ZMod 25544593197239)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (569, 1), (316153781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (569, 1), (316153781, 1)] : List FactorBlock).map factorBlockValue).prod) = 25544593197239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_71
      · exact prime_fiftyThreeAY_569
      · exact prime_fiftyThreeAY_316153781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 25544593197239) ^ 12772296598619 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 25544593197239) ^ 359783002778 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 25544593197239) ^ 44893836902 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 25544593197239) ^ 80798 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_29836538227817 : Nat.Prime 29836538227817 := by
  apply lucas_primality 29836538227817 (3 : ZMod 29836538227817)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (27223118821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (27223118821, 1)] : List FactorBlock).map factorBlockValue).prod) = 29836538227817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_137
      · exact prime_fiftyThreeAY_27223118821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29836538227817) ^ 14918269113908 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 29836538227817) ^ 217784950568 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 29836538227817) ^ 1096 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_31295135997919 : Nat.Prime 31295135997919 := by
  apply lucas_primality 31295135997919 (6 : ZMod 31295135997919)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (23, 1), (11069, 1), (58369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (23, 1), (11069, 1), (58369, 1)] : List FactorBlock).map factorBlockValue).prod) = 31295135997919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_11069
      · exact prime_fiftyThreeAY_58369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31295135997919) ^ 15647567998959 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31295135997919) ^ 10431711999306 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31295135997919) ^ 2407318153686 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31295135997919) ^ 1360658086866 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31295135997919) ^ 2827277622 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 31295135997919) ^ 536160222 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_44111984490257 : Nat.Prime 44111984490257 := by
  apply lucas_primality 44111984490257 (3 : ZMod 44111984490257)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (89213, 1), (1626503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (89213, 1), (1626503, 1)] : List FactorBlock).map factorBlockValue).prod) = 44111984490257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_89213
      · exact prime_fiftyThreeAY_1626503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44111984490257) ^ 22055992245128 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 44111984490257) ^ 2321683394224 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 44111984490257) ^ 494456912 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 44111984490257) ^ 27120752 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_49747809229949 : Nat.Prime 49747809229949 := by
  apply lucas_primality 49747809229949 (2 : ZMod 49747809229949)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1931723, 1), (6438269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1931723, 1), (6438269, 1)] : List FactorBlock).map factorBlockValue).prod) = 49747809229949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1931723
      · exact prime_fiftyThreeAY_6438269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49747809229949) ^ 24873904614974 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49747809229949) ^ 25753076 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49747809229949) ^ 7726892 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_50048179665527 : Nat.Prime 50048179665527 := by
  apply lucas_primality 50048179665527 (5 : ZMod 50048179665527)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9533, 1), (374999473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9533, 1), (374999473, 1)] : List FactorBlock).map factorBlockValue).prod) = 50048179665527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_9533
      · exact prime_fiftyThreeAY_374999473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 50048179665527) ^ 25024089832763 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50048179665527) ^ 7149739952218 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50048179665527) ^ 5249992622 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50048179665527) ^ 133462 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_64588151830879 : Nat.Prime 64588151830879 := by
  apply lucas_primality 64588151830879 (6 : ZMod 64588151830879)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (23, 1), (31, 1), (129040553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (23, 1), (31, 1), (129040553, 1)] : List FactorBlock).map factorBlockValue).prod) = 64588151830879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_129040553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 64588151830879) ^ 32294075915439 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 64588151830879) ^ 21529383943626 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 64588151830879) ^ 4968319371606 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 64588151830879) ^ 2808180514386 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 64588151830879) ^ 2083488768738 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 64588151830879) ^ 500526 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_68603121211909 : Nat.Prime 68603121211909 := by
  apply lucas_primality 68603121211909 (2 : ZMod 68603121211909)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (227, 1), (5861, 1), (4296997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (227, 1), (5861, 1), (4296997, 1)] : List FactorBlock).map factorBlockValue).prod) = 68603121211909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_227
      · exact prime_fiftyThreeAY_5861
      · exact prime_fiftyThreeAY_4296997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68603121211909) ^ 34301560605954 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 68603121211909) ^ 22867707070636 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 68603121211909) ^ 302216393004 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 68603121211909) ^ 11705019828 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 68603121211909) ^ 15965364 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_84504376625731 : Nat.Prime 84504376625731 := by
  apply lucas_primality 84504376625731 (2 : ZMod 84504376625731)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1877, 1), (11299, 1), (132817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1877, 1), (11299, 1), (132817, 1)] : List FactorBlock).map factorBlockValue).prod) = 84504376625731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_1877
      · exact prime_fiftyThreeAY_11299
      · exact prime_fiftyThreeAY_132817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84504376625731) ^ 42252188312865 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84504376625731) ^ 28168125541910 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84504376625731) ^ 16900875325146 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84504376625731) ^ 45020978490 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84504376625731) ^ 7478925270 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84504376625731) ^ 636246690 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_89357367125311 : Nat.Prime 89357367125311 := by
  apply lucas_primality 89357367125311 (6 : ZMod 89357367125311)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (491, 1), (6066352147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (491, 1), (6066352147, 1)] : List FactorBlock).map factorBlockValue).prod) = 89357367125311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_491
      · exact prime_fiftyThreeAY_6066352147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 89357367125311) ^ 44678683562655 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89357367125311) ^ 29785789041770 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89357367125311) ^ 17871473425062 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89357367125311) ^ 181990564410 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89357367125311) ^ 14730 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_89374176072317 : Nat.Prime 89374176072317 := by
  apply lucas_primality 89374176072317 (2 : ZMod 89374176072317)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1187, 1), (18823541717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1187, 1), (18823541717, 1)] : List FactorBlock).map factorBlockValue).prod) = 89374176072317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1187
      · exact prime_fiftyThreeAY_18823541717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 89374176072317) ^ 44687088036158 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 89374176072317) ^ 75294166868 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 89374176072317) ^ 4748 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_116994935220913 : Nat.Prime 116994935220913 := by
  apply lucas_primality 116994935220913 (19 : ZMod 116994935220913)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (116066403989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (116066403989, 1)] : List FactorBlock).map factorBlockValue).prod) = 116994935220913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_116066403989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 116994935220913) ^ 58497467610456 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (19 : ZMod 116994935220913) ^ 38998311740304 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (19 : ZMod 116994935220913) ^ 16713562174416 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (19 : ZMod 116994935220913) ^ 1008 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_131659656923779 : Nat.Prime 131659656923779 := by
  apply lucas_primality 131659656923779 (10 : ZMod 131659656923779)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11489, 1), (23599, 1), (80933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11489, 1), (23599, 1), (80933, 1)] : List FactorBlock).map factorBlockValue).prod) = 131659656923779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11489
      · exact prime_fiftyThreeAY_23599
      · exact prime_fiftyThreeAY_80933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 131659656923779) ^ 65829828461889 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 131659656923779) ^ 43886552307926 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 131659656923779) ^ 11459627202 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 131659656923779) ^ 5579035422 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 131659656923779) ^ 1626773466 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_153138830933237 : Nat.Prime 153138830933237 := by
  apply lucas_primality 153138830933237 (2 : ZMod 153138830933237)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (293, 1), (3391, 1), (939823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (293, 1), (3391, 1), (939823, 1)] : List FactorBlock).map factorBlockValue).prod) = 153138830933237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_293
      · exact prime_fiftyThreeAY_3391
      · exact prime_fiftyThreeAY_939823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153138830933237) ^ 76569415466618 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153138830933237) ^ 3735093437396 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153138830933237) ^ 522658126052 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153138830933237) ^ 45160374796 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153138830933237) ^ 162944332 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_191560319204729 : Nat.Prime 191560319204729 := by
  apply lucas_primality 191560319204729 (3 : ZMod 191560319204729)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (137, 1), (179, 1), (251, 1), (90469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (137, 1), (179, 1), (251, 1), (90469, 1)] : List FactorBlock).map factorBlockValue).prod) = 191560319204729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_137
      · exact prime_fiftyThreeAY_179
      · exact prime_fiftyThreeAY_251
      · exact prime_fiftyThreeAY_90469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191560319204729) ^ 95780159602364 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191560319204729) ^ 4454891144296 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191560319204729) ^ 1398250505144 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191560319204729) ^ 1070169381032 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191560319204729) ^ 763188522728 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 191560319204729) ^ 2117413912 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_200574191385361 : Nat.Prime 200574191385361 := by
  apply lucas_primality 200574191385361 (11 : ZMod 200574191385361)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (13, 1), (21428866601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (13, 1), (21428866601, 1)] : List FactorBlock).map factorBlockValue).prod) = 200574191385361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_21428866601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 200574191385361) ^ 100287095692680 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 200574191385361) ^ 66858063795120 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 200574191385361) ^ 40114838277072 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 200574191385361) ^ 15428783952720 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 200574191385361) ^ 9360 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_278102233940257 : Nat.Prime 278102233940257 := by
  apply lucas_primality 278102233940257 (7 : ZMod 278102233940257)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (11, 1), (41, 1), (713697529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (11, 1), (41, 1), (713697529, 1)] : List FactorBlock).map factorBlockValue).prod) = 278102233940257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_713697529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 278102233940257) ^ 139051116970128 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 278102233940257) ^ 92700744646752 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 278102233940257) ^ 25282021267296 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 278102233940257) ^ 6782981315616 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 278102233940257) ^ 389664 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_304988085467713 : Nat.Prime 304988085467713 := by
  apply lucas_primality 304988085467713 (5 : ZMod 304988085467713)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (529493203937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (529493203937, 1)] : List FactorBlock).map factorBlockValue).prod) = 304988085467713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_529493203937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 304988085467713) ^ 152494042733856 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 304988085467713) ^ 101662695155904 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 304988085467713) ^ 576 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_401307955432099 : Nat.Prime 401307955432099 := by
  apply lucas_primality 401307955432099 (3 : ZMod 401307955432099)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (41, 1), (167, 1), (757, 1), (90239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (41, 1), (167, 1), (757, 1), (90239, 1)] : List FactorBlock).map factorBlockValue).prod) = 401307955432099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_167
      · exact prime_fiftyThreeAY_757
      · exact prime_fiftyThreeAY_90239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 401307955432099) ^ 200653977716049 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 133769318477366 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 36482541402918 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 30869842725546 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 9787998912978 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 2403041649294 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 530129399514 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 401307955432099) ^ 4447167582 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_616953565900613 : Nat.Prime 616953565900613 := by
  apply lucas_primality 616953565900613 (2 : ZMod 616953565900613)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (211, 1), (449, 1), (1628034827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (211, 1), (449, 1), (1628034827, 1)] : List FactorBlock).map factorBlockValue).prod) = 616953565900613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_211
      · exact prime_fiftyThreeAY_449
      · exact prime_fiftyThreeAY_1628034827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 616953565900613) ^ 308476782950306 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 616953565900613) ^ 2923950549292 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 616953565900613) ^ 1374061393988 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 616953565900613) ^ 378956 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_955250548641427 : Nat.Prime 955250548641427 := by
  apply lucas_primality 955250548641427 (2 : ZMod 955250548641427)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (1145384350889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (1145384350889, 1)] : List FactorBlock).map factorBlockValue).prod) = 955250548641427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_139
      · exact prime_fiftyThreeAY_1145384350889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 955250548641427) ^ 477625274320713 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 955250548641427) ^ 318416849547142 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 955250548641427) ^ 6872306105334 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 955250548641427) ^ 834 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1125724169527519 : Nat.Prime 1125724169527519 := by
  apply lucas_primality 1125724169527519 (3 : ZMod 1125724169527519)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (259967, 1), (65609969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (259967, 1), (65609969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1125724169527519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_259967
      · exact prime_fiftyThreeAY_65609969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1125724169527519) ^ 562862084763759 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125724169527519) ^ 375241389842506 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125724169527519) ^ 102338560866138 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125724169527519) ^ 4330257954 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1125724169527519) ^ 17157822 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2197131850872577 : Nat.Prime 2197131850872577 := by
  apply lucas_primality 2197131850872577 (15 : ZMod 2197131850872577)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (17, 1), (53, 1), (199, 1), (5318581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (17, 1), (53, 1), (199, 1), (5318581, 1)] : List FactorBlock).map factorBlockValue).prod) = 2197131850872577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_199
      · exact prime_fiftyThreeAY_5318581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 2197131850872577) ^ 1098565925436288 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (15 : ZMod 2197131850872577) ^ 732377283624192 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (15 : ZMod 2197131850872577) ^ 129243050051328 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (15 : ZMod 2197131850872577) ^ 41455317940992 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (15 : ZMod 2197131850872577) ^ 11040863572224 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (15 : ZMod 2197131850872577) ^ 413104896 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3295262969270617 : Nat.Prime 3295262969270617 := by
  apply lucas_primality 3295262969270617 (5 : ZMod 3295262969270617)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (389, 1), (352963042981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (389, 1), (352963042981, 1)] : List FactorBlock).map factorBlockValue).prod) = 3295262969270617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_389
      · exact prime_fiftyThreeAY_352963042981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3295262969270617) ^ 1647631484635308 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3295262969270617) ^ 1098420989756872 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3295262969270617) ^ 8471113031544 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3295262969270617) ^ 9336 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3591279125223337 : Nat.Prime 3591279125223337 := by
  apply lucas_primality 3591279125223337 (5 : ZMod 3591279125223337)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (47, 1), (1061252696579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (47, 1), (1061252696579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3591279125223337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_1061252696579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3591279125223337) ^ 1795639562611668 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3591279125223337) ^ 1197093041741112 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3591279125223337) ^ 76410194153688 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3591279125223337) ^ 3384 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3741179980673887 : Nat.Prime 3741179980673887 := by
  apply lucas_primality 3741179980673887 (3 : ZMod 3741179980673887)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (21501034371689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (21501034371689, 1)] : List FactorBlock).map factorBlockValue).prod) = 3741179980673887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_21501034371689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3741179980673887) ^ 1870589990336943 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3741179980673887) ^ 1247059993557962 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3741179980673887) ^ 129006206230134 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3741179980673887) ^ 174 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4083758887054163 : Nat.Prime 4083758887054163 := by
  apply lucas_primality 4083758887054163 (2 : ZMod 4083758887054163)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (373, 1), (322012213141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (373, 1), (322012213141, 1)] : List FactorBlock).map factorBlockValue).prod) = 4083758887054163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_373
      · exact prime_fiftyThreeAY_322012213141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4083758887054163) ^ 2041879443527081 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4083758887054163) ^ 240221111003186 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4083758887054163) ^ 10948415246794 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4083758887054163) ^ 12682 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9353578960347901 : Nat.Prime 9353578960347901 := by
  apply lucas_primality 9353578960347901 (6 : ZMod 9353578960347901)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (501271, 1), (62199083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (501271, 1), (62199083, 1)] : List FactorBlock).map factorBlockValue).prod) = 9353578960347901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_501271
      · exact prime_fiftyThreeAY_62199083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9353578960347901) ^ 4676789480173950 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9353578960347901) ^ 3117859653449300 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9353578960347901) ^ 1870715792069580 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9353578960347901) ^ 18659724900 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9353578960347901) ^ 150381300 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9380707250486239 : Nat.Prime 9380707250486239 := by
  apply lucas_primality 9380707250486239 (6 : ZMod 9380707250486239)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8851069, 1), (58879939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8851069, 1), (58879939, 1)] : List FactorBlock).map factorBlockValue).prod) = 9380707250486239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_8851069
      · exact prime_fiftyThreeAY_58879939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9380707250486239) ^ 4690353625243119 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9380707250486239) ^ 3126902416828746 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9380707250486239) ^ 1059838902 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9380707250486239) ^ 159319242 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_19820213019777733 : Nat.Prime 19820213019777733 := by
  apply lucas_primality 19820213019777733 (2 : ZMod 19820213019777733)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23873, 1), (69186294907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23873, 1), (69186294907, 1)] : List FactorBlock).map factorBlockValue).prod) = 19820213019777733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_23873
      · exact prime_fiftyThreeAY_69186294907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19820213019777733) ^ 9910106509888866 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19820213019777733) ^ 6606737673259244 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19820213019777733) ^ 830235538884 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19820213019777733) ^ 286476 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_25866098966308009 : Nat.Prime 25866098966308009 := by
  apply lucas_primality 25866098966308009 (7 : ZMod 25866098966308009)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (18044717, 1), (59726851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (18044717, 1), (59726851, 1)] : List FactorBlock).map factorBlockValue).prod) = 25866098966308009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_18044717
      · exact prime_fiftyThreeAY_59726851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 25866098966308009) ^ 12933049483154004 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 25866098966308009) ^ 8622032988769336 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 25866098966308009) ^ 1433444424 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 25866098966308009) ^ 433073208 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_29322135463492633 : Nat.Prime 29322135463492633 := by
  apply lucas_primality 29322135463492633 (5 : ZMod 29322135463492633)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11777, 1), (103740820609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11777, 1), (103740820609, 1)] : List FactorBlock).map factorBlockValue).prod) = 29322135463492633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11777
      · exact prime_fiftyThreeAY_103740820609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29322135463492633) ^ 14661067731746316 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 29322135463492633) ^ 9774045154497544 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 29322135463492633) ^ 2489779694616 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 29322135463492633) ^ 282648 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_37890488461179061 : Nat.Prime 37890488461179061 := by
  apply lucas_primality 37890488461179061 (13 : ZMod 37890488461179061)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 2), (53, 2), (223, 1), (6858119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 2), (53, 2), (223, 1), (6858119, 1)] : List FactorBlock).map factorBlockValue).prod) = 37890488461179061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_223
      · exact prime_fiftyThreeAY_6858119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 37890488461179061) ^ 18945244230589530 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 37890488461179061) ^ 12630162820393020 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 37890488461179061) ^ 7578097692235812 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 37890488461179061) ^ 5412926923025580 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 37890488461179061) ^ 714914876626020 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 37890488461179061) ^ 169912504310220 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 37890488461179061) ^ 5524909740 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_41249117801729899 : Nat.Prime 41249117801729899 := by
  apply lucas_primality 41249117801729899 (2 : ZMod 41249117801729899)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (164653, 1), (4639287179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (164653, 1), (4639287179, 1)] : List FactorBlock).map factorBlockValue).prod) = 41249117801729899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_164653
      · exact prime_fiftyThreeAY_4639287179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41249117801729899) ^ 20624558900864949 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41249117801729899) ^ 13749705933909966 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41249117801729899) ^ 250521507666 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41249117801729899) ^ 8891262 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_77055057266673287 : Nat.Prime 77055057266673287 := by
  apply lucas_primality 77055057266673287 (5 : ZMod 77055057266673287)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61987, 1), (621542075489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61987, 1), (621542075489, 1)] : List FactorBlock).map factorBlockValue).prod) = 77055057266673287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_61987
      · exact prime_fiftyThreeAY_621542075489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 77055057266673287) ^ 38527528633336643 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 77055057266673287) ^ 1243084150978 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 77055057266673287) ^ 123974 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_94356388644506743 : Nat.Prime 94356388644506743 := by
  apply lucas_primality 94356388644506743 (3 : ZMod 94356388644506743)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2011, 1), (601540174199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2011, 1), (601540174199, 1)] : List FactorBlock).map factorBlockValue).prod) = 94356388644506743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_2011
      · exact prime_fiftyThreeAY_601540174199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94356388644506743) ^ 47178194322253371 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 94356388644506743) ^ 31452129548168914 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 94356388644506743) ^ 7258183741885134 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 94356388644506743) ^ 46920133587522 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 94356388644506743) ^ 156858 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_110958888785272309 : Nat.Prime 110958888785272309 := by
  apply lucas_primality 110958888785272309 (17 : ZMod 110958888785272309)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (19, 1), (4915775686039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (19, 1), (4915775686039, 1)] : List FactorBlock).map factorBlockValue).prod) = 110958888785272309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_4915775686039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 110958888785272309) ^ 55479444392636154 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 110958888785272309) ^ 36986296261757436 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 110958888785272309) ^ 10087171707752028 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 110958888785272309) ^ 5839941515014332 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (17 : ZMod 110958888785272309) ^ 22572 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_114755867648174209 : Nat.Prime 114755867648174209 := by
  apply lucas_primality 114755867648174209 (11 : ZMod 114755867648174209)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31, 2), (109579, 1), (2837873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31, 2), (109579, 1), (2837873, 1)] : List FactorBlock).map factorBlockValue).prod) = 114755867648174209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_109579
      · exact prime_fiftyThreeAY_2837873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 114755867648174209) ^ 57377933824087104 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 114755867648174209) ^ 38251955882724736 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 114755867648174209) ^ 3701802182199168 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 114755867648174209) ^ 1047243245952 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 114755867648174209) ^ 40437280896 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_117579611829022531 : Nat.Prime 117579611829022531 := by
  apply lucas_primality 117579611829022531 (2 : ZMod 117579611829022531)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (79, 1), (313, 1), (496876727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (79, 1), (313, 1), (496876727, 1)] : List FactorBlock).map factorBlockValue).prod) = 117579611829022531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_79
      · exact prime_fiftyThreeAY_313
      · exact prime_fiftyThreeAY_496876727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117579611829022531) ^ 58789805914511265 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 39193203943007510 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 23515922365804506 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 10689055620820230 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 4054469373414570 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 1488349516823070 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 375653711913810 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 117579611829022531) ^ 236637390 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_143531062271156377 : Nat.Prime 143531062271156377 := by
  apply lucas_primality 143531062271156377 (10 : ZMod 143531062271156377)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (31, 1), (47, 1), (67, 1), (463, 1), (491, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (31, 1), (47, 1), (67, 1), (463, 1), (491, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 143531062271156377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_67
      · exact prime_fiftyThreeAY_463
      · exact prime_fiftyThreeAY_491
      · exact prime_fiftyThreeAY_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 143531062271156377) ^ 71765531135578188 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 47843687423718792 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 4630034266811496 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 3053852388748008 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 2142254660763528 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 310002294322152 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 292323955745736 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 143531062271156377) ^ 129423861380664 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_151492425927225239 : Nat.Prime 151492425927225239 := by
  apply lucas_primality 151492425927225239 (19 : ZMod 151492425927225239)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (983, 1), (44533, 1), (1730316121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (983, 1), (44533, 1), (1730316121, 1)] : List FactorBlock).map factorBlockValue).prod) = 151492425927225239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_983
      · exact prime_fiftyThreeAY_44533
      · exact prime_fiftyThreeAY_1730316121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 151492425927225239) ^ 75746212963612619 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (19 : ZMod 151492425927225239) ^ 154112335632986 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (19 : ZMod 151492425927225239) ^ 3401801493886 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (19 : ZMod 151492425927225239) ^ 87551878 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_157614002011308551 : Nat.Prime 157614002011308551 := by
  apply lucas_primality 157614002011308551 (7 : ZMod 157614002011308551)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (23, 1), (73291, 1), (110001191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (23, 1), (73291, 1), (110001191, 1)] : List FactorBlock).map factorBlockValue).prod) = 157614002011308551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_73291
      · exact prime_fiftyThreeAY_110001191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 157614002011308551) ^ 78807001005654275 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 157614002011308551) ^ 31522800402261710 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 157614002011308551) ^ 9271411883018150 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 157614002011308551) ^ 6852782696143850 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 157614002011308551) ^ 2150523284050 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 157614002011308551) ^ 1432839050 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_172284470481095879 : Nat.Prime 172284470481095879 := by
  apply lucas_primality 172284470481095879 (7 : ZMod 172284470481095879)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (85027, 1), (53321907803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (85027, 1), (53321907803, 1)] : List FactorBlock).map factorBlockValue).prod) = 172284470481095879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_85027
      · exact prime_fiftyThreeAY_53321907803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 172284470481095879) ^ 86142235240547939 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 172284470481095879) ^ 9067603709531362 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 172284470481095879) ^ 2026232496514 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (7 : ZMod 172284470481095879) ^ 3231026 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_275558659275807799 : Nat.Prime 275558659275807799 := by
  apply lucas_primality 275558659275807799 (6 : ZMod 275558659275807799)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (139, 1), (389, 1), (431, 1), (1171, 1), (152993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (139, 1), (389, 1), (431, 1), (1171, 1), (152993, 1)] : List FactorBlock).map factorBlockValue).prod) = 275558659275807799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_139
      · exact prime_fiftyThreeAY_389
      · exact prime_fiftyThreeAY_431
      · exact prime_fiftyThreeAY_1171
      · exact prime_fiftyThreeAY_152993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 275558659275807799) ^ 137779329637903899 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 91852886425269266 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 25050787206891618 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 1982436397667682 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 708377016133182 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 639347237298858 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 235319094172338 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 275558659275807799) ^ 1801119392886 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_512096250640744529 : Nat.Prime 512096250640744529 := by
  apply lucas_primality 512096250640744529 (3 : ZMod 512096250640744529)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (19, 1), (153138830933237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (19, 1), (153138830933237, 1)] : List FactorBlock).map factorBlockValue).prod) = 512096250640744529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_153138830933237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 512096250640744529) ^ 256048125320372264 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 512096250640744529) ^ 46554204603704048 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 512096250640744529) ^ 26952434244249712 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 512096250640744529) ^ 3344 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_522480925294546523 : Nat.Prime 522480925294546523 := by
  apply lucas_primality 522480925294546523 (2 : ZMod 522480925294546523)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (479, 1), (8940773559919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (479, 1), (8940773559919, 1)] : List FactorBlock).map factorBlockValue).prod) = 522480925294546523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_61
      · exact prime_fiftyThreeAY_479
      · exact prime_fiftyThreeAY_8940773559919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 522480925294546523) ^ 261240462647273261 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 522480925294546523) ^ 8565261070402402 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 522480925294546523) ^ 1090774374310118 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 522480925294546523) ^ 58438 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_61717
      · exact prime_fiftyThreeAY_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_703731251123823193 : Nat.Prime 703731251123823193 := by
  apply lucas_primality 703731251123823193 (5 : ZMod 703731251123823193)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29322135463492633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29322135463492633, 1)] : List FactorBlock).map factorBlockValue).prod) = 703731251123823193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_29322135463492633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 703731251123823193) ^ 351865625561911596 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 703731251123823193) ^ 234577083707941064 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 703731251123823193) ^ 24 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1214038023329283809 : Nat.Prime 1214038023329283809 := by
  apply lucas_primality 1214038023329283809 (3 : ZMod 1214038023329283809)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (84487607, 1), (449044417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (84487607, 1), (449044417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1214038023329283809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_84487607
      · exact prime_fiftyThreeAY_449044417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1214038023329283809) ^ 607019011664641904 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1214038023329283809) ^ 14369421344 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1214038023329283809) ^ 2703603424 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1625545700797737437 : Nat.Prime 1625545700797737437 := by
  apply lucas_primality 1625545700797737437 (2 : ZMod 1625545700797737437)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (1125724169527519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (1125724169527519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1625545700797737437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_1125724169527519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1625545700797737437) ^ 812772850398868718 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1625545700797737437) ^ 85555036884091444 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1625545700797737437) ^ 1444 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1626077155002604027 : Nat.Prime 1626077155002604027 := by
  apply lucas_primality 1626077155002604027 (11 : ZMod 1626077155002604027)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (2909, 1), (134333, 1), (705521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (2909, 1), (134333, 1), (705521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1626077155002604027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_983
      · exact prime_fiftyThreeAY_2909
      · exact prime_fiftyThreeAY_134333
      · exact prime_fiftyThreeAY_705521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1626077155002604027) ^ 813038577501302013 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626077155002604027) ^ 542025718334201342 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626077155002604027) ^ 1654198530012822 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626077155002604027) ^ 558981490203714 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626077155002604027) ^ 12104822753922 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626077155002604027) ^ 2304789162906 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1773565586259364013 : Nat.Prime 1773565586259364013 := by
  apply lucas_primality 1773565586259364013 (2 : ZMod 1773565586259364013)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (2927, 1), (2260943641367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (2927, 1), (2260943641367, 1)] : List FactorBlock).map factorBlockValue).prod) = 1773565586259364013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_67
      · exact prime_fiftyThreeAY_2927
      · exact prime_fiftyThreeAY_2260943641367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1773565586259364013) ^ 886782793129682006 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1773565586259364013) ^ 26471128153124836 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1773565586259364013) ^ 605932895886356 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1773565586259364013) ^ 784436 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1866161847060911737 : Nat.Prime 1866161847060911737 := by
  apply lucas_primality 1866161847060911737 (5 : ZMod 1866161847060911737)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (29, 1), (353, 1), (361697965957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (29, 1), (353, 1), (361697965957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1866161847060911737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_353
      · exact prime_fiftyThreeAY_361697965957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1866161847060911737) ^ 933080923530455868 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1866161847060911737) ^ 622053949020303912 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1866161847060911737) ^ 266594549580130248 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1866161847060911737) ^ 64350408519341784 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1866161847060911737) ^ 5286577470427512 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1866161847060911737) ^ 5159448 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2397290802043790137 : Nat.Prime 2397290802043790137 := by
  apply lucas_primality 2397290802043790137 (5 : ZMod 2397290802043790137)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (139, 1), (1979, 1), (33010811279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (139, 1), (1979, 1), (33010811279, 1)] : List FactorBlock).map factorBlockValue).prod) = 2397290802043790137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_139
      · exact prime_fiftyThreeAY_1979
      · exact prime_fiftyThreeAY_33010811279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2397290802043790137) ^ 1198645401021895068 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2397290802043790137) ^ 799096934014596712 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2397290802043790137) ^ 217935527458526376 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2397290802043790137) ^ 17246696417581224 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2397290802043790137) ^ 1211364730694184 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2397290802043790137) ^ 72621384 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2428076046658567619 : Nat.Prime 2428076046658567619 := by
  apply lucas_primality 2428076046658567619 (2 : ZMod 2428076046658567619)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1214038023329283809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1214038023329283809, 1)] : List FactorBlock).map factorBlockValue).prod) = 2428076046658567619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1214038023329283809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2428076046658567619) ^ 1214038023329283809 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2428076046658567619) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2704269774582550957 : Nat.Prime 2704269774582550957 := by
  apply lucas_primality 2704269774582550957 (2 : ZMod 2704269774582550957)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (61, 1), (114167, 1), (688494517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (61, 1), (114167, 1), (688494517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2704269774582550957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_61
      · exact prime_fiftyThreeAY_114167
      · exact prime_fiftyThreeAY_688494517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2704269774582550957) ^ 1352134887291275478 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704269774582550957) ^ 901423258194183652 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704269774582550957) ^ 57537654778352148 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704269774582550957) ^ 44332291386599196 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704269774582550957) ^ 23686965362868 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704269774582550957) ^ 3927801468 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4096770005125956233 : Nat.Prime 4096770005125956233 := by
  apply lucas_primality 4096770005125956233 (3 : ZMod 4096770005125956233)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (512096250640744529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (512096250640744529, 1)] : List FactorBlock).map factorBlockValue).prod) = 4096770005125956233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_512096250640744529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4096770005125956233) ^ 2048385002562978116 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4096770005125956233) ^ 8 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4856152093317135239 : Nat.Prime 4856152093317135239 := by
  apply lucas_primality 4856152093317135239 (13 : ZMod 4856152093317135239)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2428076046658567619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2428076046658567619, 1)] : List FactorBlock).map factorBlockValue).prod) = 4856152093317135239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_2428076046658567619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 4856152093317135239) ^ 2428076046658567619 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4856152093317135239) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_5609997357451106513 : Nat.Prime 5609997357451106513 := by
  apply lucas_primality 5609997357451106513 (3 : ZMod 5609997357451106513)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (59, 1), (251, 1), (2447, 1), (3271, 1), (102001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (59, 1), (251, 1), (2447, 1), (3271, 1), (102001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5609997357451106513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_251
      · exact prime_fiftyThreeAY_2447
      · exact prime_fiftyThreeAY_3271
      · exact prime_fiftyThreeAY_102001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5609997357451106513) ^ 2804998678725553256 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5609997357451106513) ^ 193448184739693328 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5609997357451106513) ^ 95084700973747568 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5609997357451106513) ^ 22350587081478512 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5609997357451106513) ^ 2292602107662896 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5609997357451106513) ^ 1715071035601072 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5609997357451106513) ^ 54999434882512 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6511542146334284537 : Nat.Prime 6511542146334284537 := by
  apply lucas_primality 6511542146334284537 (5 : ZMod 6511542146334284537)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 2), (6619, 1), (232458705917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 2), (6619, 1), (232458705917, 1)] : List FactorBlock).map factorBlockValue).prod) = 6511542146334284537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_6619
      · exact prime_fiftyThreeAY_232458705917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6511542146334284537) ^ 3255771073167142268 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6511542146334284537) ^ 283110528101490632 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6511542146334284537) ^ 983765243440744 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6511542146334284537) ^ 28011608 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6676037877728892301 : Nat.Prime 6676037877728892301 := by
  apply lucas_primality 6676037877728892301 (2 : ZMod 6676037877728892301)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (105291073, 1), (211351817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (105291073, 1), (211351817, 1)] : List FactorBlock).map factorBlockValue).prod) = 6676037877728892301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_105291073
      · exact prime_fiftyThreeAY_211351817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6676037877728892301) ^ 3338018938864446150 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6676037877728892301) ^ 2225345959242964100 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6676037877728892301) ^ 1335207575545778460 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6676037877728892301) ^ 63405545100 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6676037877728892301) ^ 31587321900 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_7797492961813155983 : Nat.Prime 7797492961813155983 := by
  apply lucas_primality 7797492961813155983 (5 : ZMod 7797492961813155983)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47017, 1), (1439701, 1), (57596723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47017, 1), (1439701, 1), (57596723, 1)] : List FactorBlock).map factorBlockValue).prod) = 7797492961813155983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_47017
      · exact prime_fiftyThreeAY_1439701
      · exact prime_fiftyThreeAY_57596723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7797492961813155983) ^ 3898746480906577991 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7797492961813155983) ^ 165844119399646 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7797492961813155983) ^ 5416050250582 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7797492961813155983) ^ 135380843834 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9675229074948171971 : Nat.Prime 9675229074948171971 := by
  apply lucas_primality 9675229074948171971 (6 : ZMod 9675229074948171971)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (127, 1), (3505651, 1), (36832979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (127, 1), (3505651, 1), (36832979, 1)] : List FactorBlock).map factorBlockValue).prod) = 9675229074948171971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_127
      · exact prime_fiftyThreeAY_3505651
      · exact prime_fiftyThreeAY_36832979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9675229074948171971) ^ 4837614537474085985 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9675229074948171971) ^ 1935045814989634394 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9675229074948171971) ^ 163986933473697830 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9675229074948171971) ^ 76182906101954110 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9675229074948171971) ^ 2759895116470 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9675229074948171971) ^ 262678429430 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_10668003448305746107 : Nat.Prime 10668003448305746107 := by
  apply lucas_primality 10668003448305746107 (2 : ZMod 10668003448305746107)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (277, 1), (733, 1), (27279921791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (277, 1), (733, 1), (27279921791, 1)] : List FactorBlock).map factorBlockValue).prod) = 10668003448305746107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_107
      · exact prime_fiftyThreeAY_277
      · exact prime_fiftyThreeAY_733
      · exact prime_fiftyThreeAY_27279921791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10668003448305746107) ^ 5334001724152873053 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10668003448305746107) ^ 3556001149435248702 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10668003448305746107) ^ 99700966806595758 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10668003448305746107) ^ 38512647827818578 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10668003448305746107) ^ 14553892835342082 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10668003448305746107) ^ 391056966 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_11219994714902213027 : Nat.Prime 11219994714902213027 := by
  apply lucas_primality 11219994714902213027 (2 : ZMod 11219994714902213027)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5609997357451106513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5609997357451106513, 1)] : List FactorBlock).map factorBlockValue).prod) = 11219994714902213027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5609997357451106513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11219994714902213027) ^ 5609997357451106513 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11219994714902213027) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_15459319292161056889 : Nat.Prime 15459319292161056889 := by
  apply lucas_primality 15459319292161056889 (13 : ZMod 15459319292161056889)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (37890488461179061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (37890488461179061, 1)] : List FactorBlock).map factorBlockValue).prod) = 15459319292161056889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_37890488461179061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 15459319292161056889) ^ 7729659646080528444 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 15459319292161056889) ^ 5153106430720352296 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 15459319292161056889) ^ 909371723068297464 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (13 : ZMod 15459319292161056889) ^ 408 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_23509375670213412163 : Nat.Prime 23509375670213412163 := by
  apply lucas_primality 23509375670213412163 (5 : ZMod 23509375670213412163)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (173, 1), (152809, 1), (5110893259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (173, 1), (152809, 1), (5110893259, 1)] : List FactorBlock).map factorBlockValue).prod) = 23509375670213412163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_173
      · exact prime_fiftyThreeAY_152809
      · exact prime_fiftyThreeAY_5110893259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23509375670213412163) ^ 11754687835106706081 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 23509375670213412163) ^ 7836458556737804054 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 23509375670213412163) ^ 810668126559083178 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 23509375670213412163) ^ 135892344914528394 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 23509375670213412163) ^ 153848108882418 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 23509375670213412163) ^ 4599856518 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_29901823277330502229 : Nat.Prime 29901823277330502229 := by
  apply lucas_primality 29901823277330502229 (2 : ZMod 29901823277330502229)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (383, 1), (2295823, 1), (2833865591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (383, 1), (2295823, 1), (2833865591, 1)] : List FactorBlock).map factorBlockValue).prod) = 29901823277330502229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_383
      · exact prime_fiftyThreeAY_2295823
      · exact prime_fiftyThreeAY_2833865591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29901823277330502229) ^ 14950911638665251114 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29901823277330502229) ^ 9967274425776834076 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29901823277330502229) ^ 78072645632716716 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29901823277330502229) ^ 13024446256236 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29901823277330502229) ^ 10551602508 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_61822405026185802961 : Nat.Prime 61822405026185802961 := by
  apply lucas_primality 61822405026185802961 (22 : ZMod 61822405026185802961)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (167, 1), (9887, 1), (12000802727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (167, 1), (9887, 1), (12000802727, 1)] : List FactorBlock).map factorBlockValue).prod) = 61822405026185802961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_167
      · exact prime_fiftyThreeAY_9887
      · exact prime_fiftyThreeAY_12000802727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 61822405026185802961) ^ 30911202513092901480 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 61822405026185802961) ^ 20607468342061934320 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 61822405026185802961) ^ 12364481005237160592 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 61822405026185802961) ^ 4755569617398907920 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 61822405026185802961) ^ 370194042072968880 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 61822405026185802961) ^ 6252898252876080 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (22 : ZMod 61822405026185802961) ^ 5151522480 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_81277285039886871851 : Nat.Prime 81277285039886871851 := by
  apply lucas_primality 81277285039886871851 (2 : ZMod 81277285039886871851)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1625545700797737437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1625545700797737437, 1)] : List FactorBlock).map factorBlockValue).prod) = 81277285039886871851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_1625545700797737437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 81277285039886871851) ^ 40638642519943435925 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81277285039886871851) ^ 16255457007977374370 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81277285039886871851) ^ 50 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_86752709008300426537 : Nat.Prime 86752709008300426537 := by
  apply lucas_primality 86752709008300426537 (5 : ZMod 86752709008300426537)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (139, 1), (1933, 1), (462643, 1), (9692993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (139, 1), (1933, 1), (462643, 1), (9692993, 1)] : List FactorBlock).map factorBlockValue).prod) = 86752709008300426537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_139
      · exact prime_fiftyThreeAY_1933
      · exact prime_fiftyThreeAY_462643
      · exact prime_fiftyThreeAY_9692993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 86752709008300426537) ^ 43376354504150213268 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 86752709008300426537) ^ 28917569669433475512 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 86752709008300426537) ^ 624120208692808824 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 86752709008300426537) ^ 44879828767873992 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 86752709008300426537) ^ 187515447133752 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 86752709008300426537) ^ 8950043501352 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_118324989462707387557 : Nat.Prime 118324989462707387557 := by
  apply lucas_primality 118324989462707387557 (2 : ZMod 118324989462707387557)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (5101, 1), (10687, 1), (25839616007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (5101, 1), (10687, 1), (25839616007, 1)] : List FactorBlock).map factorBlockValue).prod) = 118324989462707387557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_5101
      · exact prime_fiftyThreeAY_10687
      · exact prime_fiftyThreeAY_25839616007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 118324989462707387557) ^ 59162494731353693778 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 118324989462707387557) ^ 39441663154235795852 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 118324989462707387557) ^ 16903569923243912508 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 118324989462707387557) ^ 23196430006411956 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 118324989462707387557) ^ 11071862025143388 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 118324989462707387557) ^ 4579208508 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_170326822485854643377 : Nat.Prime 170326822485854643377 := by
  apply lucas_primality 170326822485854643377 (3 : ZMod 170326822485854643377)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1823, 1), (16504577, 1), (353811541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1823, 1), (16504577, 1), (353811541, 1)] : List FactorBlock).map factorBlockValue).prod) = 170326822485854643377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1823
      · exact prime_fiftyThreeAY_16504577
      · exact prime_fiftyThreeAY_353811541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 170326822485854643377) ^ 85163411242927321688 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170326822485854643377) ^ 93432157150770512 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170326822485854643377) ^ 10319975027888 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170326822485854643377) ^ 481405501936 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_357837650994673469119 : Nat.Prime 357837650994673469119 := by
  apply lucas_primality 357837650994673469119 (3 : ZMod 357837650994673469119)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (6907, 1), (14747, 1), (11047544969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (6907, 1), (14747, 1), (11047544969, 1)] : List FactorBlock).map factorBlockValue).prod) = 357837650994673469119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_6907
      · exact prime_fiftyThreeAY_14747
      · exact prime_fiftyThreeAY_11047544969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 357837650994673469119) ^ 178918825497336734559 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 357837650994673469119) ^ 119279216998224489706 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 357837650994673469119) ^ 6751653792352329606 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 357837650994673469119) ^ 51807970319194074 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 357837650994673469119) ^ 24265115006080794 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 357837650994673469119) ^ 32390694222 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_577842113993595578167 : Nat.Prime 577842113993595578167 := by
  apply lucas_primality 577842113993595578167 (3 : ZMod 577842113993595578167)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (43, 1), (172284470481095879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (43, 1), (172284470481095879, 1)] : List FactorBlock).map factorBlockValue).prod) = 577842113993595578167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_172284470481095879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 577842113993595578167) ^ 288921056996797789083 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 577842113993595578167) ^ 192614037997865192722 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 577842113993595578167) ^ 44449393384122736782 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 577842113993595578167) ^ 13438188697525478562 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 577842113993595578167) ^ 3354 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1082693652944294955931 : Nat.Prime 1082693652944294955931 := by
  apply lucas_primality 1082693652944294955931 (10 : ZMod 1082693652944294955931)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (139, 2), (2969641954159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (139, 2), (2969641954159, 1)] : List FactorBlock).map factorBlockValue).prod) = 1082693652944294955931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_139
      · exact prime_fiftyThreeAY_2969641954159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1082693652944294955931) ^ 541346826472147477965 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1082693652944294955931) ^ 360897884314764985310 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1082693652944294955931) ^ 216538730588858991186 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1082693652944294955931) ^ 63687861937899703290 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1082693652944294955931) ^ 29261990620116079890 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1082693652944294955931) ^ 7789162970822265870 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1082693652944294955931) ^ 364587270 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2115536624322705904123 : Nat.Prime 2115536624322705904123 := by
  apply lucas_primality 2115536624322705904123 (3 : ZMod 2115536624322705904123)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (37, 1), (577, 1), (15922177, 1), (31432243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (37, 1), (577, 1), (15922177, 1), (31432243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2115536624322705904123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_577
      · exact prime_fiftyThreeAY_15922177
      · exact prime_fiftyThreeAY_31432243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2115536624322705904123) ^ 1057768312161352952061 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115536624322705904123) ^ 705178874774235301374 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115536624322705904123) ^ 192321511302064173102 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115536624322705904123) ^ 57176665522235294706 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115536624322705904123) ^ 3666441289987358586 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115536624322705904123) ^ 132867297249786 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115536624322705904123) ^ 67304666241054 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_107
      · exact prime_fiftyThreeAY_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2782591341367107154303 : Nat.Prime 2782591341367107154303 := by
  apply lucas_primality 2782591341367107154303 (3 : ZMod 2782591341367107154303)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (17, 1), (275558659275807799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (17, 1), (275558659275807799, 1)] : List FactorBlock).map factorBlockValue).prod) = 2782591341367107154303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_275558659275807799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2782591341367107154303) ^ 1391295670683553577151 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2782591341367107154303) ^ 927530447122369051434 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2782591341367107154303) ^ 252962849215191559482 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2782591341367107154303) ^ 163681843609829832606 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2782591341367107154303) ^ 10098 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_3406536449717092867541 : Nat.Prime 3406536449717092867541 := by
  apply lucas_primality 3406536449717092867541 (2 : ZMod 3406536449717092867541)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (170326822485854643377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (170326822485854643377, 1)] : List FactorBlock).map factorBlockValue).prod) = 3406536449717092867541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_170326822485854643377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3406536449717092867541) ^ 1703268224858546433770 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3406536449717092867541) ^ 681307289943418573508 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3406536449717092867541) ^ 20 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4062297111383415790001 : Nat.Prime 4062297111383415790001 := by
  apply lucas_primality 4062297111383415790001 (3 : ZMod 4062297111383415790001)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 4), (859, 1), (1201, 1), (393763550881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 4), (859, 1), (1201, 1), (393763550881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4062297111383415790001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_859
      · exact prime_fiftyThreeAY_1201
      · exact prime_fiftyThreeAY_393763550881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4062297111383415790001) ^ 2031148555691707895000 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4062297111383415790001) ^ 812459422276683158000 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4062297111383415790001) ^ 4729100246080810000 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4062297111383415790001) ^ 3382428902067790000 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4062297111383415790001) ^ 10316590000 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_4340421299563851715183 : Nat.Prime 4340421299563851715183 := by
  apply lucas_primality 4340421299563851715183 (3 : ZMod 4340421299563851715183)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (63439, 1), (367277, 1), (1149917837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (63439, 1), (367277, 1), (1149917837, 1)] : List FactorBlock).map factorBlockValue).prod) = 4340421299563851715183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_63439
      · exact prime_fiftyThreeAY_367277
      · exact prime_fiftyThreeAY_1149917837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4340421299563851715183) ^ 2170210649781925857591 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4340421299563851715183) ^ 1446807099854617238394 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4340421299563851715183) ^ 68418816494015538 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4340421299563851715183) ^ 11817841301153766 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4340421299563851715183) ^ 3774549067686 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6623838899799348693793 : Nat.Prime 6623838899799348693793 := by
  apply lucas_primality 6623838899799348693793 (5 : ZMod 6623838899799348693793)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1009, 1), (2677, 1), (25544593197239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1009, 1), (2677, 1), (25544593197239, 1)] : List FactorBlock).map factorBlockValue).prod) = 6623838899799348693793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_1009
      · exact prime_fiftyThreeAY_2677
      · exact prime_fiftyThreeAY_25544593197239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6623838899799348693793) ^ 3311919449899674346896 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6623838899799348693793) ^ 2207946299933116231264 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6623838899799348693793) ^ 6564756094944845088 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6623838899799348693793) ^ 2474351475457358496 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6623838899799348693793) ^ 259304928 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6813072899434185735083 : Nat.Prime 6813072899434185735083 := by
  apply lucas_primality 6813072899434185735083 (2 : ZMod 6813072899434185735083)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3406536449717092867541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3406536449717092867541, 1)] : List FactorBlock).map factorBlockValue).prod) = 6813072899434185735083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3406536449717092867541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6813072899434185735083) ^ 3406536449717092867541 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6813072899434185735083) ^ 2 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_8459416946558449586339 : Nat.Prime 8459416946558449586339 := by
  apply lucas_primality 8459416946558449586339 (2 : ZMod 8459416946558449586339)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (4856152093317135239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (4856152093317135239, 1)] : List FactorBlock).map factorBlockValue).prod) = 8459416946558449586339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_67
      · exact prime_fiftyThreeAY_4856152093317135239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8459416946558449586339) ^ 4229708473279224793169 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8459416946558449586339) ^ 650724380504496122026 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8459416946558449586339) ^ 126259954426245516214 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8459416946558449586339) ^ 1742 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9245473823897529250673 : Nat.Prime 9245473823897529250673 := by
  apply lucas_primality 9245473823897529250673 (3 : ZMod 9245473823897529250673)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (577842113993595578167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (577842113993595578167, 1)] : List FactorBlock).map factorBlockValue).prod) = 9245473823897529250673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_577842113993595578167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 9245473823897529250673) ^ 4622736911948764625336 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9245473823897529250673) ^ 16 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_9915828774866198365823 : Nat.Prime 9915828774866198365823 := by
  apply lucas_primality 9915828774866198365823 (5 : ZMod 9915828774866198365823)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (81277285039886871851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (81277285039886871851, 1)] : List FactorBlock).map factorBlockValue).prod) = 9915828774866198365823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_61
      · exact prime_fiftyThreeAY_81277285039886871851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9915828774866198365823) ^ 4957914387433099182911 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9915828774866198365823) ^ 162554570079773743702 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9915828774866198365823) ^ 122 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_19249908100011299288407 : Nat.Prime 19249908100011299288407 := by
  apply lucas_primality 19249908100011299288407 (3 : ZMod 19249908100011299288407)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (149, 1), (15803, 1), (2263643, 1), (14681141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (149, 1), (15803, 1), (2263643, 1), (14681141, 1)] : List FactorBlock).map factorBlockValue).prod) = 19249908100011299288407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_149
      · exact prime_fiftyThreeAY_15803
      · exact prime_fiftyThreeAY_2263643
      · exact prime_fiftyThreeAY_14681141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19249908100011299288407) ^ 9624954050005649644203 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19249908100011299288407) ^ 6416636033337099762802 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19249908100011299288407) ^ 469509953658812177766 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19249908100011299288407) ^ 129194014094035565694 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19249908100011299288407) ^ 1218117325824925602 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19249908100011299288407) ^ 8503950534607842 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19249908100011299288407) ^ 1311199728959166 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_50575731338598798952733 : Nat.Prime 50575731338598798952733 := by
  apply lucas_primality 50575731338598798952733 (2 : ZMod 50575731338598798952733)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43, 1), (3727, 1), (1618739, 1), (6962728511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43, 1), (3727, 1), (1618739, 1), (6962728511, 1)] : List FactorBlock).map factorBlockValue).prod) = 50575731338598798952733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_3727
      · exact prime_fiftyThreeAY_1618739
      · exact prime_fiftyThreeAY_6962728511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50575731338598798952733) ^ 25287865669299399476366 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50575731338598798952733) ^ 7225104476942685564676 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50575731338598798952733) ^ 1176179798572065091924 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50575731338598798952733) ^ 13570091585349825316 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50575731338598798952733) ^ 31243907349238388 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50575731338598798952733) ^ 7263780464612 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_129436633534565409509423 : Nat.Prime 129436633534565409509423 := by
  apply lucas_primality 129436633534565409509423 (5 : ZMod 129436633534565409509423)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9245473823897529250673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9245473823897529250673, 1)] : List FactorBlock).map factorBlockValue).prod) = 129436633534565409509423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_9245473823897529250673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 129436633534565409509423) ^ 64718316767282704754711 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 129436633534565409509423) ^ 18490947647795058501346 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 129436633534565409509423) ^ 14 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_240202346270277156595399 : Nat.Prime 240202346270277156595399 := by
  apply lucas_primality 240202346270277156595399 (3 : ZMod 240202346270277156595399)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (64839493, 1), (68603121211909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (64839493, 1), (68603121211909, 1)] : List FactorBlock).map factorBlockValue).prod) = 240202346270277156595399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_64839493
      · exact prime_fiftyThreeAY_68603121211909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 240202346270277156595399) ^ 120101173135138578297699 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240202346270277156595399) ^ 80067448756759052198466 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240202346270277156595399) ^ 3704568545443086 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240202346270277156595399) ^ 3501332622 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_505262628371161393203259 : Nat.Prime 505262628371161393203259 := by
  apply lucas_primality 505262628371161393203259 (2 : ZMod 505262628371161393203259)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (39827, 1), (1338013, 1), (175584222977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (39827, 1), (1338013, 1), (175584222977, 1)] : List FactorBlock).map factorBlockValue).prod) = 505262628371161393203259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_39827
      · exact prime_fiftyThreeAY_1338013
      · exact prime_fiftyThreeAY_175584222977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 505262628371161393203259) ^ 252631314185580696601629 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 505262628371161393203259) ^ 168420876123720464401086 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 505262628371161393203259) ^ 12686434538658733854 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 505262628371161393203259) ^ 377621613819268866 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 505262628371161393203259) ^ 2877608362554 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1365948267116813379942497 : Nat.Prime 1365948267116813379942497 := by
  apply lucas_primality 1365948267116813379942497 (3 : ZMod 1365948267116813379942497)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (71, 1), (19831199, 1), (572006655919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (71, 1), (19831199, 1), (572006655919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1365948267116813379942497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_71
      · exact prime_fiftyThreeAY_19831199
      · exact prime_fiftyThreeAY_572006655919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1365948267116813379942497) ^ 682974133558406689971248 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1365948267116813379942497) ^ 25772608813524780753632 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1365948267116813379942497) ^ 19238707987560751830176 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1365948267116813379942497) ^ 68878753479142304 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1365948267116813379942497) ^ 2387993658784 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_7014457053335898374353763 : Nat.Prime 7014457053335898374353763 := by
  apply lucas_primality 7014457053335898374353763 (2 : ZMod 7014457053335898374353763)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (269, 1), (73509791, 1), (9334971491081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (269, 1), (73509791, 1), (9334971491081, 1)] : List FactorBlock).map factorBlockValue).prod) = 7014457053335898374353763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_269
      · exact prime_fiftyThreeAY_73509791
      · exact prime_fiftyThreeAY_9334971491081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7014457053335898374353763) ^ 3507228526667949187176881 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7014457053335898374353763) ^ 369181950175573598650198 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7014457053335898374353763) ^ 26076048525412261614698 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7014457053335898374353763) ^ 95422078581829982 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7014457053335898374353763) ^ 751417083602 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_41773429904966386785401443 : Nat.Prime 41773429904966386785401443 := by
  apply lucas_primality 41773429904966386785401443 (5 : ZMod 41773429904966386785401443)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2904211, 1), (2397290802043790137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2904211, 1), (2397290802043790137, 1)] : List FactorBlock).map factorBlockValue).prod) = 41773429904966386785401443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_2904211
      · exact prime_fiftyThreeAY_2397290802043790137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 41773429904966386785401443) ^ 20886714952483193392700721 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 41773429904966386785401443) ^ 13924476634988795595133814 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 41773429904966386785401443) ^ 14383744812262740822 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (5 : ZMod 41773429904966386785401443) ^ 17425266 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_91341319034183061484113943 : Nat.Prime 91341319034183061484113943 := by
  apply lucas_primality 91341319034183061484113943 (10 : ZMod 91341319034183061484113943)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (989832863, 1), (2197131850872577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (989832863, 1), (2197131850872577, 1)] : List FactorBlock).map factorBlockValue).prod) = 91341319034183061484113943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_989832863
      · exact prime_fiftyThreeAY_2197131850872577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 91341319034183061484113943) ^ 45670659517091530742056971 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 91341319034183061484113943) ^ 30447106344727687161371314 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 91341319034183061484113943) ^ 13048759862026151640587706 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 91341319034183061484113943) ^ 92279537736648234 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 91341319034183061484113943) ^ 41572980246 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_167093719619865547141605773 : Nat.Prime 167093719619865547141605773 := by
  apply lucas_primality 167093719619865547141605773 (2 : ZMod 167093719619865547141605773)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41773429904966386785401443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41773429904966386785401443, 1)] : List FactorBlock).map factorBlockValue).prod) = 167093719619865547141605773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_41773429904966386785401443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 167093719619865547141605773) ^ 83546859809932773570802886 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 167093719619865547141605773) ^ 4 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_238251501359123879004190741 : Nat.Prime 238251501359123879004190741 := by
  apply lucas_primality 238251501359123879004190741 (10 : ZMod 238251501359123879004190741)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (127, 1), (3217, 1), (65123, 1), (49747809229949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (127, 1), (3217, 1), (65123, 1), (49747809229949, 1)] : List FactorBlock).map factorBlockValue).prod) = 238251501359123879004190741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_127
      · exact prime_fiftyThreeAY_3217
      · exact prime_fiftyThreeAY_65123
      · exact prime_fiftyThreeAY_49747809229949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 238251501359123879004190741) ^ 119125750679561939502095370 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 238251501359123879004190741) ^ 79417167119707959668063580 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 238251501359123879004190741) ^ 47650300271824775800838148 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 238251501359123879004190741) ^ 1875996073693888811056620 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 238251501359123879004190741) ^ 74060149629817805099220 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 238251501359123879004190741) ^ 3658484734412172028380 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (10 : ZMod 238251501359123879004190741) ^ 4789185796260 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_257860678425718436946922489 : Nat.Prime 257860678425718436946922489 := by
  apply lucas_primality 257860678425718436946922489 (89 : ZMod 257860678425718436946922489)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (214677037331, 1), (50048179665527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (214677037331, 1), (50048179665527, 1)] : List FactorBlock).map factorBlockValue).prod) = 257860678425718436946922489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_214677037331
      · exact prime_fiftyThreeAY_50048179665527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (89 : ZMod 257860678425718436946922489) ^ 128930339212859218473461244 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 257860678425718436946922489) ^ 85953559475239478982307496 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 257860678425718436946922489) ^ 1201156311972648 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 257860678425718436946922489) ^ 5152248895944 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_489532381698824845141423163 : Nat.Prime 489532381698824845141423163 := by
  apply lucas_primality 489532381698824845141423163 (2 : ZMod 489532381698824845141423163)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (240202346270277156595399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (240202346270277156595399, 1)] : List FactorBlock).map factorBlockValue).prod) = 489532381698824845141423163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_1019
      · exact prime_fiftyThreeAY_240202346270277156595399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 489532381698824845141423163) ^ 244766190849412422570711581 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 489532381698824845141423163) ^ 480404692540554313190798 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (2 : ZMod 489532381698824845141423163) ^ 2038 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1062036353516094579289867201 : Nat.Prime 1062036353516094579289867201 := by
  apply lucas_primality 1062036353516094579289867201 (79 : ZMod 1062036353516094579289867201)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1062036353516094579289867201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1062036353516094579289867201) ^ 531018176758047289644933600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 354012117838698193096622400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 212407270703218915857973440 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 151719479073727797041409600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 96548759410554052662715200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 81695104116622659945374400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 62472726677417328193521600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 55896650185057609436308800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 46175493631134546925646400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 36621943224692916527236800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 34259237210196599331931200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 28703685230164718359185600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 25903325695514501933899200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 24698519849211501843950400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 22596518159916905942337600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 20038421764454614703582400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 1062036353516094579289867201) ^ 17410432024854009496555200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1160373052915732966261151201 : Nat.Prime 1160373052915732966261151201 := by
  apply lucas_primality 1160373052915732966261151201 (6 : ZMod 1160373052915732966261151201)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160373052915732966261151201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1160373052915732966261151201) ^ 580186526457866483130575600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 232074610583146593252230240 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 165767578987961852323021600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 105488459355975724205559200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 89259465608902535866242400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 68257238406807821544773600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 61072265942933314013744800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 50451002300684042011354400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 40012863893645964353832800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 37431388803733321492295200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 31361433862587377466517600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 28301781778432511372223200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 26985419835249603866538400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 24688788359909212048109600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 21893831187089301250210400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 19667339879927677394256800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160373052915732966261151201) ^ 19022509064192343709199200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_1253202897148991603562043297 : Nat.Prime 1253202897148991603562043297 := by
  apply lucas_primality 1253202897148991603562043297 (30 : ZMod 1253202897148991603562043297)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1253202897148991603562043297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (30 : ZMod 1253202897148991603562043297) ^ 626601448574495801781021648 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 417734299049663867854014432 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 179028985306998800508863328 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 113927536104453782142003936 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 96400222857614738735541792 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 73717817479352447268355488 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 65958047218367979134844384 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 54487082484738765372262752 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 43213893005137641502139424 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 40425899908031987211678816 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 33870348571594367663839008 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 30565924320707112282001056 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 29144253422069572175861472 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 26663891428701949011958368 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 23645337682056445350227232 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 21240727070321891585797344 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (30 : ZMod 1253202897148991603562043297) ^ 20544309789327731205935136 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_2848188402611344553550098401 : Nat.Prime 2848188402611344553550098401 := by
  apply lucas_primality 2848188402611344553550098401 (89 : ZMod 2848188402611344553550098401)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848188402611344553550098401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 2848188402611344553550098401) ^ 1424094201305672276775049200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 949396134203781517850032800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 569637680522268910710019680 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 406884057515906364792871200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 219091415585488042580776800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 167540494271255561973535200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 149904652769018134397373600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 123834278374406284936960800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 98213393193494639777589600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 91877045245527243662906400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 76978064935441744690543200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 69468009819788891550002400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 66236939595612664036048800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 60599753247049884118087200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 53739403822855557614152800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 48274379705277026331357600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (89 : ZMod 2848188402611344553550098401) ^ 46691613157563025468034400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem prime_fiftyThreeAY_6962238317494397797566907201 : Nat.Prime 6962238317494397797566907201 := by
  apply lucas_primality 6962238317494397797566907201 (79 : ZMod 6962238317494397797566907201)
  · rw [← fiftyThreeAYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 6962238317494397797566907201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyThreeAY_2
      · exact prime_fiftyThreeAY_3
      · exact prime_fiftyThreeAY_5
      · exact prime_fiftyThreeAY_7
      · exact prime_fiftyThreeAY_11
      · exact prime_fiftyThreeAY_13
      · exact prime_fiftyThreeAY_17
      · exact prime_fiftyThreeAY_19
      · exact prime_fiftyThreeAY_23
      · exact prime_fiftyThreeAY_29
      · exact prime_fiftyThreeAY_31
      · exact prime_fiftyThreeAY_37
      · exact prime_fiftyThreeAY_41
      · exact prime_fiftyThreeAY_43
      · exact prime_fiftyThreeAY_47
      · exact prime_fiftyThreeAY_53
      · exact prime_fiftyThreeAY_59
      · exact prime_fiftyThreeAY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 6962238317494397797566907201) ^ 3481119158747198898783453600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 2320746105831465932522302400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 1392447663498879559513381440 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 994605473927771113938129600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 632930756135854345233355200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 535556793653415215197454400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 409543430440846929268641600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 366433595657599884082468800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 302706013804104252068126400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 240077183361875786122996800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 224588332822399928953771200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 188168603175524264799105600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 169810690670595068233339200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 161912519011497623199230400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 148132730159455272288657600 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 131362987122535807501262400 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 118004039279566064365540800 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide
    · change (79 : ZMod 6962238317494397797566907201) ^ 114135054385154062255195200 ≠ 1
      rw [← fiftyThreeAYFastPow_eq_pow]
      decide

private theorem phi_fiftyThreeAY_62660144857449580178102164800 : Nat.totient 62660144857449580178102164800 = 8245282528346113887436800000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_7, prime_fiftyThreeAY_11, prime_fiftyThreeAY_13, prime_fiftyThreeAY_17, prime_fiftyThreeAY_19, prime_fiftyThreeAY_23, prime_fiftyThreeAY_29, prime_fiftyThreeAY_31, prime_fiftyThreeAY_37, prime_fiftyThreeAY_41, prime_fiftyThreeAY_43, prime_fiftyThreeAY_47, prime_fiftyThreeAY_53, prime_fiftyThreeAY_59, prime_fiftyThreeAY_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164801 : Nat.totient 62660144857449580178102164801 = 62345269734382637710852090320 := by
  rw [← show ((([(199, 1), (2677973629, 1), (117579611829022531, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_199, prime_fiftyThreeAY_2677973629, prime_fiftyThreeAY_117579611829022531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164802 : Nat.totient 62660144857449580178102164802 = 31142463568386670806713028864 := by
  rw [← show ((([(2, 1), (167, 1), (9128923, 1), (138659057, 1), (148209875173, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_167, prime_fiftyThreeAY_9128923, prime_fiftyThreeAY_138659057, prime_fiftyThreeAY_148209875173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164803 : Nat.totient 62660144857449580178102164803 = 41182153657403259005407374080 := by
  rw [← show ((([(3, 1), (71, 1), (14153, 1), (5089829, 1), (4083758887054163, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_71, prime_fiftyThreeAY_14153, prime_fiftyThreeAY_5089829, prime_fiftyThreeAY_4083758887054163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164804 : Nat.totient 62660144857449580178102164804 = 30862459050436929234397817376 := by
  rw [← show ((([(2, 2), (67, 1), (86458279, 1), (2704269774582550957, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_67, prime_fiftyThreeAY_86458279, prime_fiftyThreeAY_2704269774582550957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164805 : Nat.totient 62660144857449580178102164805 = 50126355561259576681209953280 := by
  rw [← show ((([(5, 1), (28477, 1), (2194078213, 1), (200574191385361, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_28477, prime_fiftyThreeAY_2194078213, prime_fiftyThreeAY_200574191385361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164806 : Nat.totient 62660144857449580178102164806 = 20886706827888970625864000000 := by
  rw [← show ((([(2, 1), (3, 1), (2570801, 1), (4062297111383415790001, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_2570801, prime_fiftyThreeAY_4062297111383415790001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164807 : Nat.totient 62660144857449580178102164807 = 53452920894553257679324339200 := by
  rw [← show ((([(7, 1), (283, 1), (811, 1), (884157161, 1), (44111984490257, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_7, prime_fiftyThreeAY_283, prime_fiftyThreeAY_811, prime_fiftyThreeAY_884157161, prime_fiftyThreeAY_44111984490257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164808 : Nat.totient 62660144857449580178102164808 = 31330072397534818237780491088 := by
  rw [← show ((([(2, 3), (1004491847, 1), (7797492961813155983, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_1004491847, prime_fiftyThreeAY_7797492961813155983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164809 : Nat.totient 62660144857449580178102164809 = 41773429904966386785401443200 := by
  rw [← show ((([(3, 2), (6962238317494397797566907201, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_6962238317494397797566907201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164810 : Nat.totient 62660144857449580178102164810 = 25060822733078390839515576960 := by
  rw [← show ((([(2, 1), (5, 1), (7753, 1), (10488671, 1), (77055057266673287, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_7753, prime_fiftyThreeAY_10488671, prime_fiftyThreeAY_77055057266673287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164811 : Nat.totient 62660144857449580178102164811 = 56943358229190710482846120800 := by
  rw [← show ((([(11, 1), (2791, 1), (3308159147, 1), (616953565900613, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_11, prime_fiftyThreeAY_2791, prime_fiftyThreeAY_3308159147, prime_fiftyThreeAY_616953565900613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164812 : Nat.totient 62660144857449580178102164812 = 20886714945978884759845456848 := by
  rw [← show ((([(2, 2), (3, 1), (3211212163, 1), (1626077155002604027, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_3211212163, prime_fiftyThreeAY_1626077155002604027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164813 : Nat.totient 62660144857449580178102164813 = 57592082814293757328627621824 := by
  rw [← show ((([(13, 1), (239, 1), (9533, 1), (2115536624322705904123, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_13, prime_fiftyThreeAY_239, prime_fiftyThreeAY_9533, prime_fiftyThreeAY_2115536624322705904123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164814 : Nat.totient 62660144857449580178102164814 = 26767999403894916485043232320 := by
  rw [← show ((([(2, 1), (7, 1), (311, 1), (3846753593, 1), (3741179980673887, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_7, prime_fiftyThreeAY_311, prime_fiftyThreeAY_3846753593, prime_fiftyThreeAY_3741179980673887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164815 : Nat.totient 62660144857449580178102164815 = 33418743684758523208559521152 := by
  rw [← show ((([(3, 1), (5, 1), (139701949, 1), (29901823277330502229, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_139701949, prime_fiftyThreeAY_29901823277330502229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164816 : Nat.totient 62660144857449580178102164816 = 31070891666066237955430356480 := by
  rw [← show ((([(2, 4), (131, 1), (1553, 1), (19249908100011299288407, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_131, prime_fiftyThreeAY_1553, prime_fiftyThreeAY_19249908100011299288407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164817 : Nat.totient 62660144857449580178102164817 = 58809701871332872090047855360 := by
  rw [← show ((([(17, 1), (373, 1), (9127, 1), (1082693652944294955931, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_17, prime_fiftyThreeAY_373, prime_fiftyThreeAY_9127, prime_fiftyThreeAY_1082693652944294955931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164818 : Nat.totient 62660144857449580178102164818 = 20827400339820719371688032032 := by
  rw [← show ((([(2, 1), (3, 2), (599, 1), (853, 1), (6813072899434185735083, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_599, prime_fiftyThreeAY_853, prime_fiftyThreeAY_6813072899434185735083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164819 : Nat.totient 62660144857449580178102164819 = 59330440633860370849449738240 := by
  rw [← show ((([(19, 1), (2707, 1), (6011, 1), (79462049, 1), (2550604081537, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_19, prime_fiftyThreeAY_2707, prime_fiftyThreeAY_6011, prime_fiftyThreeAY_79462049, prime_fiftyThreeAY_2550604081537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164820 : Nat.totient 62660144857449580178102164820 = 24936814051697902285608808320 := by
  rw [← show ((([(2, 2), (5, 1), (197, 1), (1643743, 1), (9675229074948171971, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_197, prime_fiftyThreeAY_1643743, prime_fiftyThreeAY_9675229074948171971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164821 : Nat.totient 62660144857449580178102164821 = 35805190152623696916184524864 := by
  rw [← show ((([(3, 1), (7, 1), (58997, 1), (50575731338598798952733, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_7, prime_fiftyThreeAY_58997, prime_fiftyThreeAY_50575731338598798952733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164822 : Nat.totient 62660144857449580178102164822 = 28481884026113445535500984000 := by
  rw [← show ((([(2, 1), (11, 1), (2848188402611344553550098401, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_11, prime_fiftyThreeAY_2848188402611344553550098401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164823 : Nat.totient 62660144857449580178102164823 = 59320395869397641146831703040 := by
  rw [← show ((([(23, 1), (163, 1), (269, 1), (2341, 1), (66137, 1), (401307955432099, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_23, prime_fiftyThreeAY_163, prime_fiftyThreeAY_269, prime_fiftyThreeAY_2341, prime_fiftyThreeAY_66137, prime_fiftyThreeAY_401307955432099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164824 : Nat.totient 62660144857449580178102164824 = 20810172947476819844469841920 := by
  rw [← show ((([(2, 3), (3, 1), (443, 1), (709, 1), (27255071, 1), (304988085467713, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_443, prime_fiftyThreeAY_709, prime_fiftyThreeAY_27255071, prime_fiftyThreeAY_304988085467713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164825 : Nat.totient 62660144857449580178102164825 = 49631776570883859960569976000 := by
  rw [← show ((([(5, 2), (101, 1), (2326199, 1), (10668003448305746107, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_101, prime_fiftyThreeAY_2326199, prime_fiftyThreeAY_10668003448305746107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164826 : Nat.totient 62660144857449580178102164826 = 28920053651876948850292144128 := by
  rw [← show ((([(2, 1), (13, 3), (2190017, 1), (6511542146334284537, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_13, prime_fiftyThreeAY_2190017, prime_fiftyThreeAY_6511542146334284537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164827 : Nat.totient 62660144857449580178102164827 = 41773429904966386785401443056 := by
  rw [← show ((([(3, 5), (257860678425718436946922489, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_257860678425718436946922489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164828 : Nat.totient 62660144857449580178102164828 = 26661048671412925344752935680 := by
  rw [← show ((([(2, 2), (7, 1), (139, 1), (260419, 1), (61822405026185802961, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_7, prime_fiftyThreeAY_139, prime_fiftyThreeAY_260419, prime_fiftyThreeAY_61822405026185802961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164829 : Nat.totient 62660144857449580178102164829 = 59963981719365821572556390400 := by
  rw [← show ((([(29, 2), (113, 1), (847361, 1), (13764431, 1), (56531462443, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_29, prime_fiftyThreeAY_113, prime_fiftyThreeAY_847361, prime_fiftyThreeAY_13764431, prime_fiftyThreeAY_56531462443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164830 : Nat.totient 62660144857449580178102164830 = 16698327995118962036468229120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1693, 1), (14221, 1), (86752709008300426537, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_1693, prime_fiftyThreeAY_14221, prime_fiftyThreeAY_86752709008300426537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164831 : Nat.totient 62660144857449580178102164831 = 60638849862045104318883360120 := by
  rw [← show ((([(31, 1), (31295135997919, 1), (64588151830879, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_31, prime_fiftyThreeAY_31295135997919, prime_fiftyThreeAY_64588151830879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164832 : Nat.totient 62660144857449580178102164832 = 31324521583014765962124559872 := by
  rw [← show ((([(2, 5), (5693, 1), (658309, 1), (522480925294546523, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5693, prime_fiftyThreeAY_658309, prime_fiftyThreeAY_522480925294546523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164833 : Nat.totient 62660144857449580178102164833 = 37746595168899526730207063040 := by
  rw [← show ((([(3, 1), (11, 1), (193, 1), (1163, 1), (8459416946558449586339, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_11, prime_fiftyThreeAY_193, prime_fiftyThreeAY_1163, prime_fiftyThreeAY_8459416946558449586339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164834 : Nat.totient 62660144857449580178102164834 = 29487126961882389338566659072 := by
  rw [← show ((([(2, 1), (17, 1), (987559273, 1), (1866161847060911737, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_17, prime_fiftyThreeAY_987559273, prime_fiftyThreeAY_1866161847060911737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164835 : Nat.totient 62660144857449580178102164835 = 42448016651271456374005248000 := by
  rw [← show ((([(5, 1), (7, 1), (83, 1), (35401, 1), (637841, 1), (955250548641427, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_7, prime_fiftyThreeAY_83, prime_fiftyThreeAY_35401, prime_fiftyThreeAY_637841, prime_fiftyThreeAY_955250548641427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164836 : Nat.totient 62660144857449580178102164836 = 20886714670370685349251333744 := by
  rw [← show ((([(2, 2), (3, 2), (74036827, 1), (23509375670213412163, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_74036827, prime_fiftyThreeAY_23509375670213412163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164837 : Nat.totient 62660144857449580178102164837 = 60817091785572727444921804800 := by
  rw [← show ((([(37, 1), (661, 1), (1063, 1), (2971223, 1), (4244341, 1), (191121449, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_37, prime_fiftyThreeAY_661, prime_fiftyThreeAY_1063, prime_fiftyThreeAY_2971223, prime_fiftyThreeAY_4244341, prime_fiftyThreeAY_191121449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164838 : Nat.totient 62660144857449580178102164838 = 29681120248896896713186300224 := by
  rw [← show ((([(2, 1), (19, 1), (29940019, 1), (6953363107, 1), (7920649897, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_19, prime_fiftyThreeAY_29940019, prime_fiftyThreeAY_6953363107, prime_fiftyThreeAY_7920649897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164839 : Nat.totient 62660144857449580178102164839 = 38507950326516047462776195584 := by
  rw [← show ((([(3, 1), (13, 1), (829, 1), (6869, 1), (2143019, 1), (131659656923779, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_13, prime_fiftyThreeAY_829, prime_fiftyThreeAY_6869, prime_fiftyThreeAY_2143019, prime_fiftyThreeAY_131659656923779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164840 : Nat.totient 62660144857449580178102164840 = 24834112456933274895034583040 := by
  rw [← show ((([(2, 3), (5, 1), (109, 1), (75023851061, 1), (191560319204729, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_109, prime_fiftyThreeAY_75023851061, prime_fiftyThreeAY_191560319204729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164841 : Nat.totient 62660144857449580178102164841 = 61131845527773592142353843200 := by
  rw [← show ((([(41, 1), (19781833, 1), (2905653341, 1), (26588706317, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_41, prime_fiftyThreeAY_19781833, prime_fiftyThreeAY_2905653341, prime_fiftyThreeAY_26588706317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164842 : Nat.totient 62660144857449580178102164842 = 17809150856293205318224440000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (191, 1), (1170011, 1), (6676037877728892301, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_7, prime_fiftyThreeAY_191, prime_fiftyThreeAY_1170011, prime_fiftyThreeAY_6676037877728892301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164843 : Nat.totient 62660144857449580178102164843 = 61198641533193240329977651200 := by
  rw [← show ((([(43, 1), (19681, 1), (81197, 1), (143261, 1), (6365137880713, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_43, prime_fiftyThreeAY_19681, prime_fiftyThreeAY_81197, prime_fiftyThreeAY_143261, prime_fiftyThreeAY_6365137880713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164844 : Nat.totient 62660144857449580178102164844 = 28476417152079047930624005440 := by
  rw [← show ((([(2, 2), (11, 1), (5399, 1), (148723, 1), (1773565586259364013, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_11, prime_fiftyThreeAY_5399, prime_fiftyThreeAY_148723, prime_fiftyThreeAY_1773565586259364013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164845 : Nat.totient 62660144857449580178102164845 = 33418743923352321761139657216 := by
  rw [← show ((([(3, 2), (5, 1), (53832921049, 1), (25866098966308009, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_53832921049, prime_fiftyThreeAY_25866098966308009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164846 : Nat.totient 62660144857449580178102164846 = 29862815240595006606002406912 := by
  rw [← show ((([(2, 1), (23, 1), (313, 1), (4793, 1), (9623, 1), (94356388644506743, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_23, prime_fiftyThreeAY_313, prime_fiftyThreeAY_4793, prime_fiftyThreeAY_9623, prime_fiftyThreeAY_94356388644506743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164847 : Nat.totient 62660144857449580178102164847 = 61322797124252987985723080448 := by
  rw [← show ((([(47, 1), (14767, 1), (324636079, 1), (278102233940257, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_47, prime_fiftyThreeAY_14767, prime_fiftyThreeAY_324636079, prime_fiftyThreeAY_278102233940257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164848 : Nat.totient 62660144857449580178102164848 = 20622052934141192699542806528 := by
  rw [← show ((([(2, 4), (3, 1), (97, 1), (419, 1), (3975226253, 1), (8079836041819, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_97, prime_fiftyThreeAY_419, prime_fiftyThreeAY_3975226253, prime_fiftyThreeAY_8079836041819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164849 : Nat.totient 62660144857449580178102164849 = 53708417390865848580005750784 := by
  rw [← show ((([(7, 2), (193057, 1), (6623838899799348693793, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_7, prime_fiftyThreeAY_193057, prime_fiftyThreeAY_6623838899799348693793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164850 : Nat.totient 62660144857449580178102164850 = 25064057942979832071240865920 := by
  rw [← show ((([(2, 1), (5, 2), (1253202897148991603562043297, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_1253202897148991603562043297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164851 : Nat.totient 62660144857449580178102164851 = 39293316028151266572991810560 := by
  rw [← show ((([(3, 1), (17, 1), (1721, 1), (4712479, 1), (151492425927225239, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_17, prime_fiftyThreeAY_1721, prime_fiftyThreeAY_4712479, prime_fiftyThreeAY_151492425927225239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164852 : Nat.totient 62660144857449580178102164852 = 28856611280409534145355636736 := by
  rw [← show ((([(2, 2), (13, 1), (457, 1), (166823, 1), (163850273, 1), (96464774767, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_13, prime_fiftyThreeAY_457, prime_fiftyThreeAY_166823, prime_fiftyThreeAY_163850273, prime_fiftyThreeAY_96464774767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164853 : Nat.totient 62660144857449580178102164853 = 60868851048371373254050761984 := by
  rw [← show ((([(53, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_53, prime_fiftyThreeAY_103, prime_fiftyThreeAY_5009, prime_fiftyThreeAY_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164854 : Nat.totient 62660144857449580178102164854 = 20886714952483193392700721600 := by
  rw [← show ((([(2, 1), (3, 3), (1160373052915732966261151201, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_1160373052915732966261151201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164855 : Nat.totient 62660144857449580178102164855 = 45442799625877144023673324800 := by
  rw [← show ((([(5, 1), (11, 2), (691, 1), (757, 1), (21107, 1), (9380707250486239, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_11, prime_fiftyThreeAY_691, prime_fiftyThreeAY_757, prime_fiftyThreeAY_21107, prime_fiftyThreeAY_9380707250486239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164856 : Nat.totient 62660144857449580178102164856 = 26853594961559296665428616960 := by
  rw [← show ((([(2, 3), (7, 1), (35671, 1), (130887036023, 1), (239657734697, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_7, prime_fiftyThreeAY_35671, prime_fiftyThreeAY_130887036023, prime_fiftyThreeAY_239657734697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164857 : Nat.totient 62660144857449580178102164857 = 39574828330307257815504268992 := by
  rw [← show ((([(3, 1), (19, 1), (55463621197, 1), (19820213019777733, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_19, prime_fiftyThreeAY_55463621197, prime_fiftyThreeAY_19820213019777733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164858 : Nat.totient 62660144857449580178102164858 = 30229292922034023911513796096 := by
  rw [← show ((([(2, 1), (29, 1), (1493, 1), (176629, 1), (4096770005125956233, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_29, prime_fiftyThreeAY_1493, prime_fiftyThreeAY_176629, prime_fiftyThreeAY_4096770005125956233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164859 : Nat.totient 62660144857449580178102164859 = 61598108503933485598812297600 := by
  rw [← show ((([(59, 1), (1062036353516094579289867201, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_59, prime_fiftyThreeAY_1062036353516094579289867201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164860 : Nat.totient 62660144857449580178102164860 = 16709302515245761692529284672 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (240607, 1), (4340421299563851715183, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_240607, prime_fiftyThreeAY_4340421299563851715183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164861 : Nat.totient 62660144857449580178102164861 = 60788641983419701890973296000 := by
  rw [← show ((([(61, 1), (73, 1), (89277887, 1), (157614002011308551, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_61, prime_fiftyThreeAY_73, prime_fiftyThreeAY_89277887, prime_fiftyThreeAY_157614002011308551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164862 : Nat.totient 62660144857449580178102164862 = 30319404475989736637104680000 := by
  rw [← show ((([(2, 1), (31, 1), (1484281, 1), (1083819931, 1), (628241242891, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_31, prime_fiftyThreeAY_1484281, prime_fiftyThreeAY_1083819931, prime_fiftyThreeAY_628241242891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164863 : Nat.totient 62660144857449580178102164863 = 35747952477956800754300941248 := by
  rw [← show ((([(3, 2), (7, 1), (619, 1), (256528695077, 1), (6263603297927, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_7, prime_fiftyThreeAY_619, prime_fiftyThreeAY_256528695077, prime_fiftyThreeAY_6263603297927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164864 : Nat.totient 62660144857449580178102164864 = 31330072428724790089051082368 := by
  rw [← show ((([(2, 7), (489532381698824845141423163, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_489532381698824845141423163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164865 : Nat.totient 62660144857449580178102164865 = 46269799229543723907105945600 := by
  rw [← show ((([(5, 1), (13, 1), (20051, 1), (2157263419, 1), (22286343589409, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_13, prime_fiftyThreeAY_20051, prime_fiftyThreeAY_2157263419, prime_fiftyThreeAY_22286343589409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164866 : Nat.totient 62660144857449580178102164866 = 18987911878320918923046820800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1778453, 1), (147081271, 1), (3629507452427, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_11, prime_fiftyThreeAY_1778453, prime_fiftyThreeAY_147081271, prime_fiftyThreeAY_3629507452427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164867 : Nat.totient 62660144857449580178102164867 = 62658470851576862899457479680 := by
  rw [← show ((([(39341, 1), (772657, 1), (405407447, 1), (5084725753, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_39341, prime_fiftyThreeAY_772657, prime_fiftyThreeAY_405407447, prime_fiftyThreeAY_5084725753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164868 : Nat.totient 62660144857449580178102164868 = 29472739569660700775819174400 := by
  rw [← show ((([(2, 2), (17, 1), (2531, 1), (10771, 1), (61781003, 1), (547115925067, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_17, prime_fiftyThreeAY_2531, prime_fiftyThreeAY_10771, prime_fiftyThreeAY_61781003, prime_fiftyThreeAY_547115925067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164869 : Nat.totient 62660144857449580178102164869 = 39953209494312416365490750400 := by
  rw [← show ((([(3, 1), (23, 1), (10039, 1), (9671059, 1), (9353578960347901, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_23, prime_fiftyThreeAY_10039, prime_fiftyThreeAY_9671059, prime_fiftyThreeAY_9353578960347901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164870 : Nat.totient 62660144857449580178102164870 = 21481749235653602052165921792 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (15427, 1), (63913, 1), (72703469, 1), (12487271039, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_7, prime_fiftyThreeAY_15427, prime_fiftyThreeAY_63913, prime_fiftyThreeAY_72703469, prime_fiftyThreeAY_12487271039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164871 : Nat.totient 62660144857449580178102164871 = 61514037331135284646757116704 := by
  rw [← show ((([(67, 1), (293, 1), (284483, 1), (11219994714902213027, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_67, prime_fiftyThreeAY_293, prime_fiftyThreeAY_284483, prime_fiftyThreeAY_11219994714902213027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164872 : Nat.totient 62660144857449580178102164872 = 20886134708681748485297176320 := by
  rw [← show ((([(2, 3), (3, 2), (36191, 1), (6695903, 1), (3591279125223337, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_36191, prime_fiftyThreeAY_6695903, prime_fiftyThreeAY_3591279125223337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164873 : Nat.totient 62660144857449580178102164873 = 62660144857408329541234132548 := by
  rw [← show ((([(1519066302427, 1), (41249117801729899, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_1519066302427, prime_fiftyThreeAY_41249117801729899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164874 : Nat.totient 62660144857449580178102164874 = 29817325823199260774635468800 := by
  rw [← show ((([(2, 1), (37, 1), (71, 1), (127, 1), (19958322193, 1), (4705151111321, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_37, prime_fiftyThreeAY_71, prime_fiftyThreeAY_127, prime_fiftyThreeAY_19958322193, prime_fiftyThreeAY_4705151111321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164875 : Nat.totient 62660144857449580178102164875 = 33418743923973109428321154400 := by
  rw [← show ((([(3, 1), (5, 3), (167093719619865547141605773, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_167093719619865547141605773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164876 : Nat.totient 62660144857449580178102164876 = 28976136544563739135745107968 := by
  rw [← show ((([(2, 2), (19, 1), (79, 1), (89, 1), (1002290567, 1), (116994935220913, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_19, prime_fiftyThreeAY_79, prime_fiftyThreeAY_89, prime_fiftyThreeAY_1002290567, prime_fiftyThreeAY_116994935220913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164877 : Nat.totient 62660144857449580178102164877 = 48818320703896689850573601520 := by
  rw [← show ((([(7, 1), (11, 1), (6287, 1), (129436633534565409509423, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_7, prime_fiftyThreeAY_11, prime_fiftyThreeAY_6287, prime_fiftyThreeAY_129436633534565409509423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164878 : Nat.totient 62660144857449580178102164878 = 19279408282248420602197401600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (38201, 1), (146513, 1), (143531062271156377, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_13, prime_fiftyThreeAY_38201, prime_fiftyThreeAY_146513, prime_fiftyThreeAY_143531062271156377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164879 : Nat.totient 62660144857449580178102164879 = 62653130400396244279727802184 := by
  rw [← show ((([(8933, 1), (7014457053335898374353763, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_8933, prime_fiftyThreeAY_7014457053335898374353763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164880 : Nat.totient 62660144857449580178102164880 = 25058727128083918994030244864 := by
  rw [← show ((([(2, 4), (5, 1), (4799, 1), (231923, 1), (703731251123823193, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_4799, prime_fiftyThreeAY_231923, prime_fiftyThreeAY_703731251123823193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164881 : Nat.totient 62660144857449580178102164881 = 41748842836158284144562447744 := by
  rw [← show ((([(3, 3), (1699, 1), (1365948267116813379942497, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_1699, prime_fiftyThreeAY_1365948267116813379942497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164882 : Nat.totient 62660144857449580178102164882 = 30565923702334340593581596160 := by
  rw [← show ((([(2, 1), (41, 1), (49429609, 1), (15459319292161056889, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_41, prime_fiftyThreeAY_49429609, prime_fiftyThreeAY_15459319292161056889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164883 : Nat.totient 62660144857449580178102164883 = 62421893356090456299097973880 := by
  rw [← show ((([(263, 1), (238251501359123879004190741, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_263, prime_fiftyThreeAY_238251501359123879004190741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164884 : Nat.totient 62660144857449580178102164884 = 17801835099463236212614978560 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (179, 1), (17387, 1), (1001831, 1), (3358889, 1), (71226943, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_7, prime_fiftyThreeAY_179, prime_fiftyThreeAY_17387, prime_fiftyThreeAY_1001831, prime_fiftyThreeAY_3358889, prime_fiftyThreeAY_71226943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164885 : Nat.totient 62660144857449580178102164885 = 47147066378569811922582410496 := by
  rw [← show ((([(5, 1), (17, 1), (1459, 1), (505262628371161393203259, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_17, prime_fiftyThreeAY_1459, prime_fiftyThreeAY_505262628371161393203259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164886 : Nat.totient 62660144857449580178102164886 = 30600478772934312362778685440 := by
  rw [← show ((([(2, 1), (43, 1), (38069, 1), (166781, 1), (114755867648174209, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_43, prime_fiftyThreeAY_38069, prime_fiftyThreeAY_166781, prime_fiftyThreeAY_114755867648174209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164887 : Nat.totient 62660144857449580178102164887 = 40332960178595722156708893312 := by
  rw [← show ((([(3, 1), (29, 1), (6086893, 1), (118324989462707387557, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_29, prime_fiftyThreeAY_6086893, prime_fiftyThreeAY_118324989462707387557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164888 : Nat.totient 62660144857449580178102164888 = 28355112489787085919571776000 := by
  rw [← show ((([(2, 3), (11, 1), (227, 1), (21803, 1), (263488741, 1), (546014967781, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_11, prime_fiftyThreeAY_227, prime_fiftyThreeAY_21803, prime_fiftyThreeAY_263488741, prime_fiftyThreeAY_546014967781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164889 : Nat.totient 62660144857449580178102164889 = 62660139198125221737059526000 := by
  rw [← show ((([(14301451, 1), (49032149, 1), (89357367125311, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_14301451, prime_fiftyThreeAY_49032149, prime_fiftyThreeAY_89357367125311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164890 : Nat.totient 62660144857449580178102164890 = 16588696540694146011086803200 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (151, 1), (1657, 1), (2782591341367107154303, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_5, prime_fiftyThreeAY_151, prime_fiftyThreeAY_1657, prime_fiftyThreeAY_2782591341367107154303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164891 : Nat.totient 62660144857449580178102164891 = 49577064846160695426132117120 := by
  rw [← show ((([(7, 1), (13, 1), (259631, 1), (29674363, 1), (89374176072317, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_7, prime_fiftyThreeAY_13, prime_fiftyThreeAY_259631, prime_fiftyThreeAY_29674363, prime_fiftyThreeAY_89374176072317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164892 : Nat.totient 62660144857449580178102164892 = 29967459070140226842013395248 := by
  rw [← show ((([(2, 2), (23, 1), (68687, 1), (9915828774866198365823, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_23, prime_fiftyThreeAY_68687, prime_fiftyThreeAY_9915828774866198365823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164893 : Nat.totient 62660144857449580178102164893 = 40045811911898464946138086080 := by
  rw [← show ((([(3, 1), (31, 1), (107, 1), (17597, 1), (357837650994673469119, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_31, prime_fiftyThreeAY_107, prime_fiftyThreeAY_17597, prime_fiftyThreeAY_357837650994673469119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164894 : Nat.totient 62660144857449580178102164894 = 30662410142149343805000499200 := by
  rw [← show ((([(2, 1), (47, 1), (30497, 1), (984421, 1), (1079933, 1), (20560266481, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_47, prime_fiftyThreeAY_30497, prime_fiftyThreeAY_984421, prime_fiftyThreeAY_1079933, prime_fiftyThreeAY_20560266481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164895 : Nat.totient 62660144857449580178102164895 = 47489091537614810211002117376 := by
  rw [← show ((([(5, 1), (19, 1), (67619, 1), (326926867, 1), (29836538227817, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_5, prime_fiftyThreeAY_19, prime_fiftyThreeAY_67619, prime_fiftyThreeAY_326926867, prime_fiftyThreeAY_29836538227817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164896 : Nat.totient 62660144857449580178102164896 = 20878537431508465162768782336 := by
  rw [← show ((([(2, 5), (3, 1), (2557, 1), (2300527, 1), (110958888785272309, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_3, prime_fiftyThreeAY_2557, prime_fiftyThreeAY_2300527, prime_fiftyThreeAY_110958888785272309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164897 : Nat.totient 62660144857449580178102164897 = 62655504356990744402934931200 := by
  rw [← show ((([(16381, 1), (77023, 1), (33816241, 1), (1468605749659, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_16381, prime_fiftyThreeAY_77023, prime_fiftyThreeAY_33816241, prime_fiftyThreeAY_1468605749659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164898 : Nat.totient 62660144857449580178102164898 = 26854347796049820076329498948 := by
  rw [← show ((([(2, 1), (7, 3), (91341319034183061484113943, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_7, prime_fiftyThreeAY_91341319034183061484113943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164899 : Nat.totient 62660144857449580178102164899 = 37974671633772550699131916800 := by
  rw [← show ((([(3, 2), (11, 1), (32533, 1), (5903941, 1), (3295262969270617, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_3, prime_fiftyThreeAY_11, prime_fiftyThreeAY_32533, prime_fiftyThreeAY_5903941, prime_fiftyThreeAY_3295262969270617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyThreeAY_62660144857449580178102164900 : Nat.totient 62660144857449580178102164900 = 25064057942976155295467757600 := by
  rw [← show ((([(2, 2), (5, 2), (7415017701979, 1), (84504376625731, 1)] : List FactorBlock).map factorBlockValue).prod) = 62660144857449580178102164900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyThreeAY_2, prime_fiftyThreeAY_5, prime_fiftyThreeAY_7415017701979, prime_fiftyThreeAY_84504376625731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyThreeAY : certifiedKill 1 62660144857449580178102164799 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyThreeAY_62660144857449580178102164800, phi_fiftyThreeAY_62660144857449580178102164801, phi_fiftyThreeAY_62660144857449580178102164802,
    phi_fiftyThreeAY_62660144857449580178102164803, phi_fiftyThreeAY_62660144857449580178102164804, phi_fiftyThreeAY_62660144857449580178102164805,
    phi_fiftyThreeAY_62660144857449580178102164806, phi_fiftyThreeAY_62660144857449580178102164807, phi_fiftyThreeAY_62660144857449580178102164808,
    phi_fiftyThreeAY_62660144857449580178102164809, phi_fiftyThreeAY_62660144857449580178102164810, phi_fiftyThreeAY_62660144857449580178102164811,
    phi_fiftyThreeAY_62660144857449580178102164812, phi_fiftyThreeAY_62660144857449580178102164813, phi_fiftyThreeAY_62660144857449580178102164814,
    phi_fiftyThreeAY_62660144857449580178102164815, phi_fiftyThreeAY_62660144857449580178102164816, phi_fiftyThreeAY_62660144857449580178102164817,
    phi_fiftyThreeAY_62660144857449580178102164818, phi_fiftyThreeAY_62660144857449580178102164819, phi_fiftyThreeAY_62660144857449580178102164820,
    phi_fiftyThreeAY_62660144857449580178102164821, phi_fiftyThreeAY_62660144857449580178102164822, phi_fiftyThreeAY_62660144857449580178102164823,
    phi_fiftyThreeAY_62660144857449580178102164824, phi_fiftyThreeAY_62660144857449580178102164825, phi_fiftyThreeAY_62660144857449580178102164826,
    phi_fiftyThreeAY_62660144857449580178102164827, phi_fiftyThreeAY_62660144857449580178102164828, phi_fiftyThreeAY_62660144857449580178102164829,
    phi_fiftyThreeAY_62660144857449580178102164830, phi_fiftyThreeAY_62660144857449580178102164831, phi_fiftyThreeAY_62660144857449580178102164832,
    phi_fiftyThreeAY_62660144857449580178102164833, phi_fiftyThreeAY_62660144857449580178102164834, phi_fiftyThreeAY_62660144857449580178102164835,
    phi_fiftyThreeAY_62660144857449580178102164836, phi_fiftyThreeAY_62660144857449580178102164837, phi_fiftyThreeAY_62660144857449580178102164838,
    phi_fiftyThreeAY_62660144857449580178102164839, phi_fiftyThreeAY_62660144857449580178102164840, phi_fiftyThreeAY_62660144857449580178102164841,
    phi_fiftyThreeAY_62660144857449580178102164842, phi_fiftyThreeAY_62660144857449580178102164843, phi_fiftyThreeAY_62660144857449580178102164844,
    phi_fiftyThreeAY_62660144857449580178102164845, phi_fiftyThreeAY_62660144857449580178102164846, phi_fiftyThreeAY_62660144857449580178102164847,
    phi_fiftyThreeAY_62660144857449580178102164848, phi_fiftyThreeAY_62660144857449580178102164849, phi_fiftyThreeAY_62660144857449580178102164850,
    phi_fiftyThreeAY_62660144857449580178102164851, phi_fiftyThreeAY_62660144857449580178102164852, phi_fiftyThreeAY_62660144857449580178102164853,
    phi_fiftyThreeAY_62660144857449580178102164854, phi_fiftyThreeAY_62660144857449580178102164855, phi_fiftyThreeAY_62660144857449580178102164856,
    phi_fiftyThreeAY_62660144857449580178102164857, phi_fiftyThreeAY_62660144857449580178102164858, phi_fiftyThreeAY_62660144857449580178102164859,
    phi_fiftyThreeAY_62660144857449580178102164860, phi_fiftyThreeAY_62660144857449580178102164861, phi_fiftyThreeAY_62660144857449580178102164862,
    phi_fiftyThreeAY_62660144857449580178102164863, phi_fiftyThreeAY_62660144857449580178102164864, phi_fiftyThreeAY_62660144857449580178102164865,
    phi_fiftyThreeAY_62660144857449580178102164866, phi_fiftyThreeAY_62660144857449580178102164867, phi_fiftyThreeAY_62660144857449580178102164868,
    phi_fiftyThreeAY_62660144857449580178102164869, phi_fiftyThreeAY_62660144857449580178102164870, phi_fiftyThreeAY_62660144857449580178102164871,
    phi_fiftyThreeAY_62660144857449580178102164872, phi_fiftyThreeAY_62660144857449580178102164873, phi_fiftyThreeAY_62660144857449580178102164874,
    phi_fiftyThreeAY_62660144857449580178102164875, phi_fiftyThreeAY_62660144857449580178102164876, phi_fiftyThreeAY_62660144857449580178102164877,
    phi_fiftyThreeAY_62660144857449580178102164878, phi_fiftyThreeAY_62660144857449580178102164879, phi_fiftyThreeAY_62660144857449580178102164880,
    phi_fiftyThreeAY_62660144857449580178102164881, phi_fiftyThreeAY_62660144857449580178102164882, phi_fiftyThreeAY_62660144857449580178102164883,
    phi_fiftyThreeAY_62660144857449580178102164884, phi_fiftyThreeAY_62660144857449580178102164885, phi_fiftyThreeAY_62660144857449580178102164886,
    phi_fiftyThreeAY_62660144857449580178102164887, phi_fiftyThreeAY_62660144857449580178102164888, phi_fiftyThreeAY_62660144857449580178102164889,
    phi_fiftyThreeAY_62660144857449580178102164890, phi_fiftyThreeAY_62660144857449580178102164891, phi_fiftyThreeAY_62660144857449580178102164892,
    phi_fiftyThreeAY_62660144857449580178102164893, phi_fiftyThreeAY_62660144857449580178102164894, phi_fiftyThreeAY_62660144857449580178102164895,
    phi_fiftyThreeAY_62660144857449580178102164896, phi_fiftyThreeAY_62660144857449580178102164897, phi_fiftyThreeAY_62660144857449580178102164898,
    phi_fiftyThreeAY_62660144857449580178102164899, phi_fiftyThreeAY_62660144857449580178102164900]

end TotientTailPeriodKiller
end Erdos249257
