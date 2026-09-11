import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtyEightAJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyEightAJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyEightAJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyEightAJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyEightAJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyEightAJFastPow a n * thirtyEightAJFastPow a n * a
        else thirtyEightAJFastPow a n * thirtyEightAJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyEightAJ_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtyEightAJ_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtyEightAJ_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtyEightAJ_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtyEightAJ_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtyEightAJ_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtyEightAJ_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtyEightAJ_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtyEightAJ_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtyEightAJ_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtyEightAJ_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtyEightAJ_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtyEightAJ_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtyEightAJ_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtyEightAJ_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtyEightAJ_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtyEightAJ_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtyEightAJ_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtyEightAJ_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtyEightAJ_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtyEightAJ_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtyEightAJ_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtyEightAJ_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtyEightAJ_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtyEightAJ_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtyEightAJ_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtyEightAJ_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtyEightAJ_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtyEightAJ_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtyEightAJ_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtyEightAJ_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtyEightAJ_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtyEightAJ_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtyEightAJ_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtyEightAJ_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtyEightAJ_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtyEightAJ_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirtyEightAJ_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtyEightAJ_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtyEightAJ_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtyEightAJ_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirtyEightAJ_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtyEightAJ_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtyEightAJ_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtyEightAJ_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtyEightAJ_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtyEightAJ_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtyEightAJ_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirtyEightAJ_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtyEightAJ_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtyEightAJ_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtyEightAJ_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtyEightAJ_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirtyEightAJ_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtyEightAJ_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirtyEightAJ_283 : Nat.Prime 283 := by norm_num
private theorem prime_thirtyEightAJ_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirtyEightAJ_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtyEightAJ_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtyEightAJ_337 : Nat.Prime 337 := by norm_num
private theorem prime_thirtyEightAJ_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtyEightAJ_349 : Nat.Prime 349 := by norm_num
private theorem prime_thirtyEightAJ_353 : Nat.Prime 353 := by norm_num
private theorem prime_thirtyEightAJ_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirtyEightAJ_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirtyEightAJ_373 : Nat.Prime 373 := by norm_num
private theorem prime_thirtyEightAJ_379 : Nat.Prime 379 := by norm_num
private theorem prime_thirtyEightAJ_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtyEightAJ_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirtyEightAJ_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtyEightAJ_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtyEightAJ_421 : Nat.Prime 421 := by norm_num
private theorem prime_thirtyEightAJ_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtyEightAJ_439 : Nat.Prime 439 := by norm_num
private theorem prime_thirtyEightAJ_443 : Nat.Prime 443 := by norm_num
private theorem prime_thirtyEightAJ_449 : Nat.Prime 449 := by norm_num
private theorem prime_thirtyEightAJ_461 : Nat.Prime 461 := by norm_num
private theorem prime_thirtyEightAJ_467 : Nat.Prime 467 := by norm_num
private theorem prime_thirtyEightAJ_479 : Nat.Prime 479 := by norm_num
private theorem prime_thirtyEightAJ_487 : Nat.Prime 487 := by norm_num
private theorem prime_thirtyEightAJ_523 : Nat.Prime 523 := by norm_num
private theorem prime_thirtyEightAJ_541 : Nat.Prime 541 := by norm_num
private theorem prime_thirtyEightAJ_569 : Nat.Prime 569 := by norm_num
private theorem prime_thirtyEightAJ_571 : Nat.Prime 571 := by norm_num
private theorem prime_thirtyEightAJ_577 : Nat.Prime 577 := by norm_num
private theorem prime_thirtyEightAJ_593 : Nat.Prime 593 := by norm_num
private theorem prime_thirtyEightAJ_601 : Nat.Prime 601 := by norm_num
private theorem prime_thirtyEightAJ_617 : Nat.Prime 617 := by norm_num
private theorem prime_thirtyEightAJ_641 : Nat.Prime 641 := by norm_num
private theorem prime_thirtyEightAJ_653 : Nat.Prime 653 := by norm_num
private theorem prime_thirtyEightAJ_661 : Nat.Prime 661 := by norm_num
private theorem prime_thirtyEightAJ_677 : Nat.Prime 677 := by norm_num
private theorem prime_thirtyEightAJ_691 : Nat.Prime 691 := by norm_num
private theorem prime_thirtyEightAJ_709 : Nat.Prime 709 := by norm_num
private theorem prime_thirtyEightAJ_719 : Nat.Prime 719 := by norm_num
private theorem prime_thirtyEightAJ_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtyEightAJ_733 : Nat.Prime 733 := by norm_num
private theorem prime_thirtyEightAJ_743 : Nat.Prime 743 := by norm_num
private theorem prime_thirtyEightAJ_757 : Nat.Prime 757 := by norm_num
private theorem prime_thirtyEightAJ_769 : Nat.Prime 769 := by norm_num
private theorem prime_thirtyEightAJ_811 : Nat.Prime 811 := by norm_num
private theorem prime_thirtyEightAJ_823 : Nat.Prime 823 := by norm_num
private theorem prime_thirtyEightAJ_827 : Nat.Prime 827 := by norm_num
private theorem prime_thirtyEightAJ_829 : Nat.Prime 829 := by norm_num
private theorem prime_thirtyEightAJ_839 : Nat.Prime 839 := by norm_num
private theorem prime_thirtyEightAJ_853 : Nat.Prime 853 := by norm_num
private theorem prime_thirtyEightAJ_857 : Nat.Prime 857 := by norm_num
private theorem prime_thirtyEightAJ_907 : Nat.Prime 907 := by norm_num
private theorem prime_thirtyEightAJ_911 : Nat.Prime 911 := by norm_num
private theorem prime_thirtyEightAJ_953 : Nat.Prime 953 := by norm_num
private theorem prime_thirtyEightAJ_983 : Nat.Prime 983 := by norm_num
private theorem prime_thirtyEightAJ_997 : Nat.Prime 997 := by norm_num
private theorem prime_thirtyEightAJ_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_thirtyEightAJ_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_thirtyEightAJ_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_thirtyEightAJ_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_thirtyEightAJ_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_thirtyEightAJ_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_thirtyEightAJ_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_thirtyEightAJ_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_thirtyEightAJ_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_thirtyEightAJ_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_thirtyEightAJ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_thirtyEightAJ_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_thirtyEightAJ_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_thirtyEightAJ_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_thirtyEightAJ_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_thirtyEightAJ_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_thirtyEightAJ_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_thirtyEightAJ_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_thirtyEightAJ_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_thirtyEightAJ_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_thirtyEightAJ_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_thirtyEightAJ_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_thirtyEightAJ_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_thirtyEightAJ_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_thirtyEightAJ_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_thirtyEightAJ_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_thirtyEightAJ_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_thirtyEightAJ_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_thirtyEightAJ_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_thirtyEightAJ_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_thirtyEightAJ_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_thirtyEightAJ_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_thirtyEightAJ_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_thirtyEightAJ_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtyEightAJ_2543 : Nat.Prime 2543 := by norm_num
private theorem prime_thirtyEightAJ_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_thirtyEightAJ_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_thirtyEightAJ_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_thirtyEightAJ_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_thirtyEightAJ_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_thirtyEightAJ_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_thirtyEightAJ_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_thirtyEightAJ_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_thirtyEightAJ_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_thirtyEightAJ_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_thirtyEightAJ_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_thirtyEightAJ_3881 : Nat.Prime 3881 := by norm_num
private theorem prime_thirtyEightAJ_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_thirtyEightAJ_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_thirtyEightAJ_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_thirtyEightAJ_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_thirtyEightAJ_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_thirtyEightAJ_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_thirtyEightAJ_4447 : Nat.Prime 4447 := by norm_num
private theorem prime_thirtyEightAJ_4729 : Nat.Prime 4729 := by norm_num
private theorem prime_thirtyEightAJ_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_thirtyEightAJ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtyEightAJ_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_thirtyEightAJ_5261 : Nat.Prime 5261 := by norm_num
private theorem prime_thirtyEightAJ_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_thirtyEightAJ_5783 : Nat.Prime 5783 := by norm_num
private theorem prime_thirtyEightAJ_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_thirtyEightAJ_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_thirtyEightAJ_6199 : Nat.Prime 6199 := by norm_num
private theorem prime_thirtyEightAJ_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_thirtyEightAJ_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_thirtyEightAJ_6637 : Nat.Prime 6637 := by norm_num
private theorem prime_thirtyEightAJ_6719 : Nat.Prime 6719 := by norm_num
private theorem prime_thirtyEightAJ_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtyEightAJ_6917 : Nat.Prime 6917 := by norm_num
private theorem prime_thirtyEightAJ_6967 : Nat.Prime 6967 := by norm_num
private theorem prime_thirtyEightAJ_7457 : Nat.Prime 7457 := by norm_num
private theorem prime_thirtyEightAJ_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_thirtyEightAJ_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_thirtyEightAJ_7487 : Nat.Prime 7487 := by norm_num
private theorem prime_thirtyEightAJ_7499 : Nat.Prime 7499 := by norm_num
private theorem prime_thirtyEightAJ_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_thirtyEightAJ_8147 : Nat.Prime 8147 := by norm_num
private theorem prime_thirtyEightAJ_8387 : Nat.Prime 8387 := by norm_num
private theorem prime_thirtyEightAJ_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_thirtyEightAJ_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_thirtyEightAJ_8627 : Nat.Prime 8627 := by norm_num
private theorem prime_thirtyEightAJ_8941 : Nat.Prime 8941 := by norm_num
private theorem prime_thirtyEightAJ_8969 : Nat.Prime 8969 := by norm_num
private theorem prime_thirtyEightAJ_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_thirtyEightAJ_9239 : Nat.Prime 9239 := by norm_num
private theorem prime_thirtyEightAJ_9439 : Nat.Prime 9439 := by norm_num
private theorem prime_thirtyEightAJ_10079 : Nat.Prime 10079 := by norm_num
private theorem prime_thirtyEightAJ_10151 : Nat.Prime 10151 := by norm_num
private theorem prime_thirtyEightAJ_10253 : Nat.Prime 10253 := by norm_num
private theorem prime_thirtyEightAJ_11551 : Nat.Prime 11551 := by norm_num
private theorem prime_thirtyEightAJ_12413 : Nat.Prime 12413 := by norm_num
private theorem prime_thirtyEightAJ_12487 : Nat.Prime 12487 := by norm_num
private theorem prime_thirtyEightAJ_12899 : Nat.Prime 12899 := by norm_num
private theorem prime_thirtyEightAJ_13009 : Nat.Prime 13009 := by norm_num
private theorem prime_thirtyEightAJ_13151 : Nat.Prime 13151 := by norm_num
private theorem prime_thirtyEightAJ_14293 : Nat.Prime 14293 := by norm_num
private theorem prime_thirtyEightAJ_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_thirtyEightAJ_16333 : Nat.Prime 16333 := by norm_num
private theorem prime_thirtyEightAJ_16349 : Nat.Prime 16349 := by norm_num
private theorem prime_thirtyEightAJ_17419 : Nat.Prime 17419 := by norm_num
private theorem prime_thirtyEightAJ_17911 : Nat.Prime 17911 := by norm_num
private theorem prime_thirtyEightAJ_17923 : Nat.Prime 17923 := by norm_num
private theorem prime_thirtyEightAJ_17987 : Nat.Prime 17987 := by norm_num
private theorem prime_thirtyEightAJ_18233 : Nat.Prime 18233 := by norm_num
private theorem prime_thirtyEightAJ_18251 : Nat.Prime 18251 := by norm_num
private theorem prime_thirtyEightAJ_19489 : Nat.Prime 19489 := by norm_num
private theorem prime_thirtyEightAJ_20681 : Nat.Prime 20681 := by norm_num
private theorem prime_thirtyEightAJ_21011 : Nat.Prime 21011 := by norm_num
private theorem prime_thirtyEightAJ_21191 : Nat.Prime 21191 := by norm_num
private theorem prime_thirtyEightAJ_21481 : Nat.Prime 21481 := by norm_num
private theorem prime_thirtyEightAJ_21493 : Nat.Prime 21493 := by norm_num
private theorem prime_thirtyEightAJ_23041 : Nat.Prime 23041 := by norm_num
private theorem prime_thirtyEightAJ_23087 : Nat.Prime 23087 := by norm_num
private theorem prime_thirtyEightAJ_25523 : Nat.Prime 25523 := by norm_num
private theorem prime_thirtyEightAJ_25841 : Nat.Prime 25841 := by norm_num
private theorem prime_thirtyEightAJ_27631 : Nat.Prime 27631 := by norm_num
private theorem prime_thirtyEightAJ_29473 : Nat.Prime 29473 := by norm_num
private theorem prime_thirtyEightAJ_29531 : Nat.Prime 29531 := by norm_num
private theorem prime_thirtyEightAJ_30689 : Nat.Prime 30689 := by norm_num
private theorem prime_thirtyEightAJ_33359 : Nat.Prime 33359 := by norm_num
private theorem prime_thirtyEightAJ_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtyEightAJ_35419 : Nat.Prime 35419 := by norm_num
private theorem prime_thirtyEightAJ_36497 : Nat.Prime 36497 := by norm_num
private theorem prime_thirtyEightAJ_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtyEightAJ_37813 : Nat.Prime 37813 := by norm_num
private theorem prime_thirtyEightAJ_38873 : Nat.Prime 38873 := by norm_num
private theorem prime_thirtyEightAJ_39047 : Nat.Prime 39047 := by norm_num
private theorem prime_thirtyEightAJ_39343 : Nat.Prime 39343 := by norm_num
private theorem prime_thirtyEightAJ_39521 : Nat.Prime 39521 := by norm_num
private theorem prime_thirtyEightAJ_40099 : Nat.Prime 40099 := by norm_num
private theorem prime_thirtyEightAJ_41593 : Nat.Prime 41593 := by norm_num
private theorem prime_thirtyEightAJ_41669 : Nat.Prime 41669 := by norm_num
private theorem prime_thirtyEightAJ_54413 : Nat.Prime 54413 := by norm_num
private theorem prime_thirtyEightAJ_54877 : Nat.Prime 54877 := by norm_num
private theorem prime_thirtyEightAJ_56633 : Nat.Prime 56633 := by norm_num
private theorem prime_thirtyEightAJ_57493 : Nat.Prime 57493 := by norm_num
private theorem prime_thirtyEightAJ_58237 : Nat.Prime 58237 := by norm_num
private theorem prime_thirtyEightAJ_59629 : Nat.Prime 59629 := by norm_num
private theorem prime_thirtyEightAJ_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtyEightAJ_62401 : Nat.Prime 62401 := by norm_num
private theorem prime_thirtyEightAJ_64033 : Nat.Prime 64033 := by norm_num
private theorem prime_thirtyEightAJ_65419 : Nat.Prime 65419 := by norm_num
private theorem prime_thirtyEightAJ_66587 : Nat.Prime 66587 := by norm_num
private theorem prime_thirtyEightAJ_71707 : Nat.Prime 71707 := by norm_num
private theorem prime_thirtyEightAJ_72533 : Nat.Prime 72533 := by norm_num
private theorem prime_thirtyEightAJ_76471 : Nat.Prime 76471 := by norm_num
private theorem prime_thirtyEightAJ_77587 : Nat.Prime 77587 := by norm_num
private theorem prime_thirtyEightAJ_77929 : Nat.Prime 77929 := by norm_num
private theorem prime_thirtyEightAJ_81929 : Nat.Prime 81929 := by norm_num
private theorem prime_thirtyEightAJ_82219 : Nat.Prime 82219 := by norm_num
private theorem prime_thirtyEightAJ_85903 : Nat.Prime 85903 := by norm_num
private theorem prime_thirtyEightAJ_86183 : Nat.Prime 86183 := by norm_num
private theorem prime_thirtyEightAJ_89891 : Nat.Prime 89891 := by norm_num
private theorem prime_thirtyEightAJ_91199 : Nat.Prime 91199 := by norm_num
private theorem prime_thirtyEightAJ_93169 : Nat.Prime 93169 := by norm_num
private theorem prime_thirtyEightAJ_101173 : Nat.Prime 101173 := by norm_num
private theorem prime_thirtyEightAJ_102673 : Nat.Prime 102673 := by norm_num
private theorem prime_thirtyEightAJ_104323 : Nat.Prime 104323 := by norm_num
private theorem prime_thirtyEightAJ_113731 : Nat.Prime 113731 := by norm_num
private theorem prime_thirtyEightAJ_126613 : Nat.Prime 126613 := by norm_num
private theorem prime_thirtyEightAJ_131203 : Nat.Prime 131203 := by norm_num
private theorem prime_thirtyEightAJ_133499 : Nat.Prime 133499 := by norm_num
private theorem prime_thirtyEightAJ_133781 : Nat.Prime 133781 := by norm_num
private theorem prime_thirtyEightAJ_139939 : Nat.Prime 139939 := by norm_num
private theorem prime_thirtyEightAJ_145031 : Nat.Prime 145031 := by norm_num
private theorem prime_thirtyEightAJ_151939 : Nat.Prime 151939 := by norm_num
private theorem prime_thirtyEightAJ_154061 : Nat.Prime 154061 := by norm_num
private theorem prime_thirtyEightAJ_156641 : Nat.Prime 156641 := by norm_num
private theorem prime_thirtyEightAJ_166027 : Nat.Prime 166027 := by norm_num
private theorem prime_thirtyEightAJ_172169 : Nat.Prime 172169 := by norm_num
private theorem prime_thirtyEightAJ_181499 : Nat.Prime 181499 := by norm_num
private theorem prime_thirtyEightAJ_184409 : Nat.Prime 184409 := by norm_num
private theorem prime_thirtyEightAJ_185233 : Nat.Prime 185233 := by norm_num
private theorem prime_thirtyEightAJ_186161 : Nat.Prime 186161 := by norm_num
private theorem prime_thirtyEightAJ_200867 : Nat.Prime 200867 := by norm_num
private theorem prime_thirtyEightAJ_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_thirtyEightAJ_210499 : Nat.Prime 210499 := by norm_num
private theorem prime_thirtyEightAJ_225529 : Nat.Prime 225529 := by norm_num
private theorem prime_thirtyEightAJ_227663 : Nat.Prime 227663 := by norm_num
private theorem prime_thirtyEightAJ_246833 : Nat.Prime 246833 := by norm_num
private theorem prime_thirtyEightAJ_248033 : Nat.Prime 248033 := by norm_num
private theorem prime_thirtyEightAJ_271217 : Nat.Prime 271217 := by norm_num
private theorem prime_thirtyEightAJ_286103 : Nat.Prime 286103 := by norm_num
private theorem prime_thirtyEightAJ_306533 : Nat.Prime 306533 := by norm_num
private theorem prime_thirtyEightAJ_328667 : Nat.Prime 328667 := by norm_num
private theorem prime_thirtyEightAJ_338263 : Nat.Prime 338263 := by norm_num
private theorem prime_thirtyEightAJ_347071 : Nat.Prime 347071 := by norm_num
private theorem prime_thirtyEightAJ_354469 : Nat.Prime 354469 := by norm_num
private theorem prime_thirtyEightAJ_368609 : Nat.Prime 368609 := by norm_num
private theorem prime_thirtyEightAJ_390581 : Nat.Prime 390581 := by norm_num
private theorem prime_thirtyEightAJ_442439 : Nat.Prime 442439 := by norm_num
private theorem prime_thirtyEightAJ_443909 : Nat.Prime 443909 := by norm_num
private theorem prime_thirtyEightAJ_506381 : Nat.Prime 506381 := by norm_num
private theorem prime_thirtyEightAJ_507641 : Nat.Prime 507641 := by norm_num
private theorem prime_thirtyEightAJ_566233 : Nat.Prime 566233 := by norm_num
private theorem prime_thirtyEightAJ_620111 : Nat.Prime 620111 := by norm_num
private theorem prime_thirtyEightAJ_628561 : Nat.Prime 628561 := by norm_num
private theorem prime_thirtyEightAJ_660817 : Nat.Prime 660817 := by norm_num
private theorem prime_thirtyEightAJ_712321 : Nat.Prime 712321 := by norm_num
private theorem prime_thirtyEightAJ_764521 : Nat.Prime 764521 := by norm_num
private theorem prime_thirtyEightAJ_777181 : Nat.Prime 777181 := by norm_num
private theorem prime_thirtyEightAJ_821497 : Nat.Prime 821497 := by norm_num
private theorem prime_thirtyEightAJ_828743 : Nat.Prime 828743 := by norm_num
private theorem prime_thirtyEightAJ_886759 : Nat.Prime 886759 := by norm_num
private theorem prime_thirtyEightAJ_1000099 : Nat.Prime 1000099 := by norm_num
private theorem prime_thirtyEightAJ_1011079 : Nat.Prime 1011079 := by norm_num
private theorem prime_thirtyEightAJ_1016641 : Nat.Prime 1016641 := by norm_num
private theorem prime_thirtyEightAJ_1042043 : Nat.Prime 1042043 := by norm_num
private theorem prime_thirtyEightAJ_1042523 : Nat.Prime 1042523 := by norm_num
private theorem prime_thirtyEightAJ_1083319 : Nat.Prime 1083319 := by norm_num
private theorem prime_thirtyEightAJ_1183003 : Nat.Prime 1183003 := by norm_num
private theorem prime_thirtyEightAJ_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_thirtyEightAJ_1239523 : Nat.Prime 1239523 := by norm_num
private theorem prime_thirtyEightAJ_1315597 : Nat.Prime 1315597 := by norm_num
private theorem prime_thirtyEightAJ_1318411 : Nat.Prime 1318411 := by norm_num
private theorem prime_thirtyEightAJ_1419373 : Nat.Prime 1419373 := by norm_num
private theorem prime_thirtyEightAJ_1434941 : Nat.Prime 1434941 := by norm_num
private theorem prime_thirtyEightAJ_1497407 : Nat.Prime 1497407 := by norm_num
private theorem prime_thirtyEightAJ_1715783 : Nat.Prime 1715783 := by norm_num
private theorem prime_thirtyEightAJ_1725697 : Nat.Prime 1725697 := by norm_num
private theorem prime_thirtyEightAJ_1917341 : Nat.Prime 1917341 := by norm_num
private theorem prime_thirtyEightAJ_1961107 : Nat.Prime 1961107 := by norm_num
private theorem prime_thirtyEightAJ_1962997 : Nat.Prime 1962997 := by norm_num
private theorem prime_thirtyEightAJ_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_thirtyEightAJ_2158727 : Nat.Prime 2158727 := by norm_num
private theorem prime_thirtyEightAJ_2212631 : Nat.Prime 2212631 := by norm_num
private theorem prime_thirtyEightAJ_2217557 : Nat.Prime 2217557 := by norm_num
private theorem prime_thirtyEightAJ_2241989 : Nat.Prime 2241989 := by norm_num
private theorem prime_thirtyEightAJ_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_thirtyEightAJ_2650463 : Nat.Prime 2650463 := by norm_num
private theorem prime_thirtyEightAJ_2685967 : Nat.Prime 2685967 := by norm_num
private theorem prime_thirtyEightAJ_2912887 : Nat.Prime 2912887 := by norm_num
private theorem prime_thirtyEightAJ_2912891 : Nat.Prime 2912891 := by norm_num
private theorem prime_thirtyEightAJ_2971909 : Nat.Prime 2971909 := by norm_num
private theorem prime_thirtyEightAJ_2976671 : Nat.Prime 2976671 := by norm_num
private theorem prime_thirtyEightAJ_3014237 : Nat.Prime 3014237 := by norm_num
private theorem prime_thirtyEightAJ_3033581 : Nat.Prime 3033581 := by norm_num
private theorem prime_thirtyEightAJ_3182359 : Nat.Prime 3182359 := by norm_num
private theorem prime_thirtyEightAJ_3199561 : Nat.Prime 3199561 := by norm_num
private theorem prime_thirtyEightAJ_3327677 : Nat.Prime 3327677 := by norm_num
private theorem prime_thirtyEightAJ_3352277 : Nat.Prime 3352277 := by norm_num
private theorem prime_thirtyEightAJ_3714331 : Nat.Prime 3714331 := by norm_num
private theorem prime_thirtyEightAJ_3930517 : Nat.Prime 3930517 := by norm_num
private theorem prime_thirtyEightAJ_4014937 : Nat.Prime 4014937 := by norm_num
private theorem prime_thirtyEightAJ_4058011 : Nat.Prime 4058011 := by norm_num
private theorem prime_thirtyEightAJ_4520393 : Nat.Prime 4520393 := by norm_num
private theorem prime_thirtyEightAJ_4624393 : Nat.Prime 4624393 := by norm_num
private theorem prime_thirtyEightAJ_5144533 : Nat.Prime 5144533 := by norm_num
private theorem prime_thirtyEightAJ_5261701 : Nat.Prime 5261701 := by norm_num
private theorem prime_thirtyEightAJ_5387951 : Nat.Prime 5387951 := by norm_num
private theorem prime_thirtyEightAJ_5501341 : Nat.Prime 5501341 := by norm_num
private theorem prime_thirtyEightAJ_6168143 : Nat.Prime 6168143 := by norm_num
private theorem prime_thirtyEightAJ_7006843 : Nat.Prime 7006843 := by norm_num
private theorem prime_thirtyEightAJ_7032919 : Nat.Prime 7032919 := by norm_num
private theorem prime_thirtyEightAJ_7125277 : Nat.Prime 7125277 := by norm_num
private theorem prime_thirtyEightAJ_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtyEightAJ_7863253 : Nat.Prime 7863253 := by norm_num
private theorem prime_thirtyEightAJ_8148493 : Nat.Prime 8148493 := by norm_num
private theorem prime_thirtyEightAJ_9718361 : Nat.Prime 9718361 := by norm_num
private theorem prime_thirtyEightAJ_10279219 : Nat.Prime 10279219 := by norm_num
private theorem prime_thirtyEightAJ_10911689 : Nat.Prime 10911689 := by norm_num
private theorem prime_thirtyEightAJ_11416631 : Nat.Prime 11416631 := by norm_num
private theorem prime_thirtyEightAJ_11912603 : Nat.Prime 11912603 := by norm_num
private theorem prime_thirtyEightAJ_12797297 : Nat.Prime 12797297 := by norm_num
private theorem prime_thirtyEightAJ_13250177 : Nat.Prime 13250177 := by norm_num
private theorem prime_thirtyEightAJ_14238023 : Nat.Prime 14238023 := by norm_num
private theorem prime_thirtyEightAJ_14408221 : Nat.Prime 14408221 := by norm_num
private theorem prime_thirtyEightAJ_14774317 : Nat.Prime 14774317 := by norm_num
private theorem prime_thirtyEightAJ_17327003 : Nat.Prime 17327003 := by norm_num
private theorem prime_thirtyEightAJ_18394897 : Nat.Prime 18394897 := by norm_num
private theorem prime_thirtyEightAJ_18499207 : Nat.Prime 18499207 := by norm_num
private theorem prime_thirtyEightAJ_19015481 : Nat.Prime 19015481 := by norm_num
private theorem prime_thirtyEightAJ_21345371 : Nat.Prime 21345371 := by norm_num
private theorem prime_thirtyEightAJ_21953167 : Nat.Prime 21953167 := by norm_num
private theorem prime_thirtyEightAJ_22638193 : Nat.Prime 22638193 := by norm_num
private theorem prime_thirtyEightAJ_23974079 : Nat.Prime 23974079 := by norm_num
private theorem prime_thirtyEightAJ_24337051 : Nat.Prime 24337051 := by norm_num
private theorem prime_thirtyEightAJ_26713663 : Nat.Prime 26713663 := by norm_num
private theorem prime_thirtyEightAJ_27974873 : Nat.Prime 27974873 := by norm_num

private theorem prime_thirtyEightAJ_30757451 : Nat.Prime 30757451 := by
  apply lucas_primality 30757451 (6 : ZMod 30757451)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (617, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (617, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) = 30757451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_617
      · exact prime_thirtyEightAJ_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 30757451) ^ 15378725 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 30757451) ^ 6151490 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 30757451) ^ 49850 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 30757451) ^ 30850 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_983
      · exact prime_thirtyEightAJ_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_36571693 : Nat.Prime 36571693 := by
  apply lucas_primality 36571693 (2 : ZMod 36571693)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (31, 1), (5783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (31, 1), (5783, 1)] : List FactorBlock).map factorBlockValue).prod) = 36571693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_5783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36571693) ^ 18285846 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571693) ^ 12190564 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571693) ^ 2151276 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571693) ^ 1179732 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571693) ^ 6324 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_40443383 : Nat.Prime 40443383 := by
  apply lucas_primality 40443383 (5 : ZMod 40443383)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (569, 1), (5077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (569, 1), (5077, 1)] : List FactorBlock).map factorBlockValue).prod) = 40443383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_569
      · exact prime_thirtyEightAJ_5077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40443383) ^ 20221691 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40443383) ^ 5777626 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40443383) ^ 71078 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40443383) ^ 7966 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_42041059 : Nat.Prime 42041059 := by
  apply lucas_primality 42041059 (2 : ZMod 42041059)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7006843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7006843, 1)] : List FactorBlock).map factorBlockValue).prod) = 42041059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7006843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42041059) ^ 21020529 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 42041059) ^ 14013686 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 42041059) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_43086893 : Nat.Prime 43086893 := by
  apply lucas_primality 43086893 (2 : ZMod 43086893)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (601, 1), (17923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (601, 1), (17923, 1)] : List FactorBlock).map factorBlockValue).prod) = 43086893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_601
      · exact prime_thirtyEightAJ_17923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43086893) ^ 21543446 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 43086893) ^ 71692 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 43086893) ^ 2404 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_49146259 : Nat.Prime 49146259 := by
  apply lucas_primality 49146259 (7 : ZMod 49146259)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (409, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (409, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 49146259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_409
      · exact prime_thirtyEightAJ_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 49146259) ^ 24573129 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 16382086 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 7020894 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 120162 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 17178 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_52362491 : Nat.Prime 52362491 := by
  apply lucas_primality 52362491 (2 : ZMod 52362491)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (227663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (227663, 1)] : List FactorBlock).map factorBlockValue).prod) = 52362491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_227663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52362491) ^ 26181245 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52362491) ^ 10472498 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52362491) ^ 2276630 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52362491) ^ 230 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_53225903 : Nat.Prime 53225903 := by
  apply lucas_primality 53225903 (5 : ZMod 53225903)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (566233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (566233, 1)] : List FactorBlock).map factorBlockValue).prod) = 53225903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_566233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 53225903) ^ 26612951 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53225903) ^ 1132466 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53225903) ^ 94 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_59767193 : Nat.Prime 59767193 := by
  apply lucas_primality 59767193 (3 : ZMod 59767193)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (72533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (72533, 1)] : List FactorBlock).map factorBlockValue).prod) = 59767193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_103
      · exact prime_thirtyEightAJ_72533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59767193) ^ 29883596 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59767193) ^ 580264 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59767193) ^ 824 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_73579589 : Nat.Prime 73579589 := by
  apply lucas_primality 73579589 (2 : ZMod 73579589)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18394897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18394897, 1)] : List FactorBlock).map factorBlockValue).prod) = 73579589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_18394897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 73579589) ^ 36789794 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73579589) ^ 4 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_78438047 : Nat.Prime 78438047 := by
  apply lucas_primality 78438047 (5 : ZMod 78438047)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (347071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (347071, 1)] : List FactorBlock).map factorBlockValue).prod) = 78438047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_113
      · exact prime_thirtyEightAJ_347071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 78438047) ^ 39219023 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 78438047) ^ 694142 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 78438047) ^ 226 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_79559329 : Nat.Prime 79559329 := by
  apply lucas_primality 79559329 (7 : ZMod 79559329)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (828743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (828743, 1)] : List FactorBlock).map factorBlockValue).prod) = 79559329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_828743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 79559329) ^ 39779664 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 79559329) ^ 26519776 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 79559329) ^ 96 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_85171937 : Nat.Prime 85171937 := by
  apply lucas_primality 85171937 (3 : ZMod 85171937)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (103, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (103, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) = 85171937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_103
      · exact prime_thirtyEightAJ_25841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 85171937) ^ 42585968 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 85171937) ^ 826912 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 85171937) ^ 3296 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_88645903 : Nat.Prime 88645903 := by
  apply lucas_primality 88645903 (3 : ZMod 88645903)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14774317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14774317, 1)] : List FactorBlock).map factorBlockValue).prod) = 88645903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_14774317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 88645903) ^ 44322951 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 88645903) ^ 29548634 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 88645903) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_110631551 : Nat.Prime 110631551 := by
  apply lucas_primality 110631551 (7 : ZMod 110631551)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2212631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2212631, 1)] : List FactorBlock).map factorBlockValue).prod) = 110631551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_2212631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 110631551) ^ 55315775 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 110631551) ^ 22126310 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 110631551) ^ 50 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_114600677 : Nat.Prime 114600677 := by
  apply lucas_primality 114600677 (3 : ZMod 114600677)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (43, 1), (21493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (43, 1), (21493, 1)] : List FactorBlock).map factorBlockValue).prod) = 114600677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_21493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 114600677) ^ 57300338 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 114600677) ^ 3696796 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 114600677) ^ 2665132 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 114600677) ^ 5332 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_114795281 : Nat.Prime 114795281 := by
  apply lucas_primality 114795281 (3 : ZMod 114795281)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1434941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1434941, 1)] : List FactorBlock).map factorBlockValue).prod) = 114795281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_1434941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 114795281) ^ 57397640 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 114795281) ^ 22959056 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 114795281) ^ 80 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_128926417 : Nat.Prime 128926417 := by
  apply lucas_primality 128926417 (5 : ZMod 128926417)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2685967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2685967, 1)] : List FactorBlock).map factorBlockValue).prod) = 128926417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_2685967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 128926417) ^ 64463208 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 128926417) ^ 42975472 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 128926417) ^ 48 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_129713707 : Nat.Prime 129713707 := by
  apply lucas_primality 129713707 (5 : ZMod 129713707)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (109, 1), (3889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (109, 1), (3889, 1)] : List FactorBlock).map factorBlockValue).prod) = 129713707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_109
      · exact prime_thirtyEightAJ_3889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 129713707) ^ 64856853 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 43237902 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 7630218 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 1190034 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 33354 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_131192779 : Nat.Prime 131192779 := by
  apply lucas_primality 131192779 (11 : ZMod 131192779)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (172169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (172169, 1)] : List FactorBlock).map factorBlockValue).prod) = 131192779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_127
      · exact prime_thirtyEightAJ_172169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 131192779) ^ 65596389 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 131192779) ^ 43730926 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 131192779) ^ 1033014 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 131192779) ^ 762 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_150860029 : Nat.Prime 150860029 := by
  apply lucas_primality 150860029 (2 : ZMod 150860029)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (257, 1), (4447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (257, 1), (4447, 1)] : List FactorBlock).map factorBlockValue).prod) = 150860029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_257
      · exact prime_thirtyEightAJ_4447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150860029) ^ 75430014 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150860029) ^ 50286676 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150860029) ^ 13714548 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150860029) ^ 587004 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150860029) ^ 33924 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_153387281 : Nat.Prime 153387281 := by
  apply lucas_primality 153387281 (3 : ZMod 153387281)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1917341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1917341, 1)] : List FactorBlock).map factorBlockValue).prod) = 153387281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_1917341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 153387281) ^ 76693640 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153387281) ^ 30677456 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153387281) ^ 80 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_154228859 : Nat.Prime 154228859 := by
  apply lucas_primality 154228859 (2 : ZMod 154228859)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1093, 1), (10079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1093, 1), (10079, 1)] : List FactorBlock).map factorBlockValue).prod) = 154228859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_1093
      · exact prime_thirtyEightAJ_10079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 154228859) ^ 77114429 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 154228859) ^ 22032694 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 154228859) ^ 141106 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 154228859) ^ 15302 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_158598107 : Nat.Prime 158598107 := by
  apply lucas_primality 158598107 (2 : ZMod 158598107)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5261, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5261, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) = 158598107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5261
      · exact prime_thirtyEightAJ_15073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158598107) ^ 79299053 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 158598107) ^ 30146 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 158598107) ^ 10522 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_171220741 : Nat.Prime 171220741 := by
  apply lucas_primality 171220741 (7 : ZMod 171220741)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (53, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (53, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) = 171220741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 171220741) ^ 85610370 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 171220741) ^ 57073580 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 171220741) ^ 34244148 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 171220741) ^ 7444380 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 171220741) ^ 3230580 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 171220741) ^ 73140 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_176345227 : Nat.Prime 176345227 := by
  apply lucas_primality 176345227 (3 : ZMod 176345227)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (157, 1), (62401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (157, 1), (62401, 1)] : List FactorBlock).map factorBlockValue).prod) = 176345227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_157
      · exact prime_thirtyEightAJ_62401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 176345227) ^ 88172613 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176345227) ^ 58781742 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176345227) ^ 1123218 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176345227) ^ 2826 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_189651827 : Nat.Prime 189651827 := by
  apply lucas_primality 189651827 (5 : ZMod 189651827)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (1042043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (1042043, 1)] : List FactorBlock).map factorBlockValue).prod) = 189651827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_1042043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 189651827) ^ 94825913 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 189651827) ^ 27093118 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 189651827) ^ 14588602 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 189651827) ^ 182 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_191
      · exact prime_thirtyEightAJ_383
      · exact prime_thirtyEightAJ_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_253697251 : Nat.Prime 253697251 := by
  apply lucas_primality 253697251 (10 : ZMod 253697251)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (338263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (338263, 1)] : List FactorBlock).map factorBlockValue).prod) = 253697251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_338263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 253697251) ^ 126848625 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 253697251) ^ 84565750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 253697251) ^ 50739450 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 253697251) ^ 750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_254872777 : Nat.Prime 254872777 := by
  apply lucas_primality 254872777 (5 : ZMod 254872777)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (743, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (743, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) = 254872777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_743
      · exact prime_thirtyEightAJ_14293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 254872777) ^ 127436388 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 254872777) ^ 84957592 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 254872777) ^ 343032 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 254872777) ^ 17832 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_282797033 : Nat.Prime 282797033 := by
  apply lucas_primality 282797033 (3 : ZMod 282797033)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (757, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (757, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 282797033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_757
      · exact prime_thirtyEightAJ_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 282797033) ^ 141398516 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 282797033) ^ 40399576 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 282797033) ^ 373576 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 282797033) ^ 296744 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_299113201 : Nat.Prime 299113201 := by
  apply lucas_primality 299113201 (11 : ZMod 299113201)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (19, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (19, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) = 299113201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_4373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 299113201) ^ 149556600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 299113201) ^ 99704400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 299113201) ^ 59822640 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 299113201) ^ 15742800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 299113201) ^ 68400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_356352497 : Nat.Prime 356352497 := by
  apply lucas_primality 356352497 (3 : ZMod 356352497)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47, 1), (53, 1), (8941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47, 1), (53, 1), (8941, 1)] : List FactorBlock).map factorBlockValue).prod) = 356352497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_8941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 356352497) ^ 178176248 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 356352497) ^ 7581968 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 356352497) ^ 6723632 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 356352497) ^ 39856 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_359419759 : Nat.Prime 359419759 := by
  apply lucas_primality 359419759 (6 : ZMod 359419759)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (67, 1), (38873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (67, 1), (38873, 1)] : List FactorBlock).map factorBlockValue).prod) = 359419759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_38873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 359419759) ^ 179709879 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 119806586 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 15626946 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 5364474 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 9246 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_380903827 : Nat.Prime 380903827 := by
  apply lucas_primality 380903827 (2 : ZMod 380903827)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1715783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1715783, 1)] : List FactorBlock).map factorBlockValue).prod) = 380903827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_1715783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 380903827) ^ 190451913 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 380903827) ^ 126967942 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 380903827) ^ 10294698 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 380903827) ^ 222 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_394349519 : Nat.Prime 394349519 := by
  apply lucas_primality 394349519 (7 : ZMod 394349519)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (727, 1), (271217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (727, 1), (271217, 1)] : List FactorBlock).map factorBlockValue).prod) = 394349519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_727
      · exact prime_thirtyEightAJ_271217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 394349519) ^ 197174759 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 394349519) ^ 542434 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 394349519) ^ 1454 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_400263187 : Nat.Prime 400263187 := by
  apply lucas_primality 400263187 (2 : ZMod 400263187)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (1419373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (1419373, 1)] : List FactorBlock).map factorBlockValue).prod) = 400263187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_1419373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 400263187) ^ 200131593 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 400263187) ^ 133421062 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 400263187) ^ 8516238 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 400263187) ^ 282 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_454695737 : Nat.Prime 454695737 := by
  apply lucas_primality 454695737 (3 : ZMod 454695737)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (17, 1), (27631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (17, 1), (27631, 1)] : List FactorBlock).map factorBlockValue).prod) = 454695737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_27631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 454695737) ^ 227347868 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 454695737) ^ 41335976 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 454695737) ^ 26746808 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 454695737) ^ 16456 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_495245143 : Nat.Prime 495245143 := by
  apply lucas_primality 495245143 (3 : ZMod 495245143)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3930517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3930517, 1)] : List FactorBlock).map factorBlockValue).prod) = 495245143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_3930517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 495245143) ^ 247622571 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 495245143) ^ 165081714 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 495245143) ^ 70749306 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 495245143) ^ 126 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_515705669 : Nat.Prime 515705669 := by
  apply lucas_primality 515705669 (2 : ZMod 515705669)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (128926417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (128926417, 1)] : List FactorBlock).map factorBlockValue).prod) = 515705669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_128926417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 515705669) ^ 257852834 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 515705669) ^ 4 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_546633823 : Nat.Prime 546633823 := by
  apply lucas_primality 546633823 (3 : ZMod 546633823)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1009, 1), (12899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1009, 1), (12899, 1)] : List FactorBlock).map factorBlockValue).prod) = 546633823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_1009
      · exact prime_thirtyEightAJ_12899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 546633823) ^ 273316911 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 546633823) ^ 182211274 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 546633823) ^ 78090546 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 546633823) ^ 541758 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 546633823) ^ 42378 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_547396931 : Nat.Prime 547396931 := by
  apply lucas_primality 547396931 (2 : ZMod 547396931)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6719, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6719, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) = 547396931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_6719
      · exact prime_thirtyEightAJ_8147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 547396931) ^ 273698465 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 547396931) ^ 109479386 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 547396931) ^ 81470 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 547396931) ^ 67190 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_619561331 : Nat.Prime 619561331 := by
  apply lucas_primality 619561331 (2 : ZMod 619561331)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1129, 1), (54877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1129, 1), (54877, 1)] : List FactorBlock).map factorBlockValue).prod) = 619561331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_1129
      · exact prime_thirtyEightAJ_54877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 619561331) ^ 309780665 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619561331) ^ 123912266 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619561331) ^ 548770 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619561331) ^ 11290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_661543237 : Nat.Prime 661543237 := by
  apply lucas_primality 661543237 (2 : ZMod 661543237)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (47, 1), (109, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (47, 1), (109, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 661543237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_109
      · exact prime_thirtyEightAJ_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 661543237) ^ 330771618 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 661543237) ^ 220514412 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 661543237) ^ 38914308 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 661543237) ^ 14075388 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 661543237) ^ 6069204 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 661543237) ^ 3135276 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_663789307 : Nat.Prime 663789307 := by
  apply lucas_primality 663789307 (3 : ZMod 663789307)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (110631551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (110631551, 1)] : List FactorBlock).map factorBlockValue).prod) = 663789307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_110631551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 663789307) ^ 331894653 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 663789307) ^ 221263102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 663789307) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_791502073 : Nat.Prime 791502073 := by
  apply lucas_primality 791502073 (5 : ZMod 791502073)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4969, 1), (6637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4969, 1), (6637, 1)] : List FactorBlock).map factorBlockValue).prod) = 791502073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_4969
      · exact prime_thirtyEightAJ_6637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 791502073) ^ 395751036 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 791502073) ^ 263834024 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 791502073) ^ 159288 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 791502073) ^ 119256 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1000658653 : Nat.Prime 1000658653 := by
  apply lucas_primality 1000658653 (15 : ZMod 1000658653)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11912603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11912603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1000658653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11912603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 1000658653) ^ 500329326 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 1000658653) ^ 333552884 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 1000658653) ^ 142951236 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 1000658653) ^ 84 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1063750837 : Nat.Prime 1063750837 := by
  apply lucas_primality 1063750837 (5 : ZMod 1063750837)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (88645903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (88645903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063750837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_88645903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1063750837) ^ 531875418 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063750837) ^ 354583612 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063750837) ^ 12 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1080175511 : Nat.Prime 1080175511 := by
  apply lucas_primality 1080175511 (14 : ZMod 1080175511)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (97, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (97, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080175511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_97
      · exact prime_thirtyEightAJ_21011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1080175511) ^ 540087755 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1080175511) ^ 216035102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1080175511) ^ 20380670 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1080175511) ^ 11135830 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1080175511) ^ 51410 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1116057143 : Nat.Prime 1116057143 := by
  apply lucas_primality 1116057143 (5 : ZMod 1116057143)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1021, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1021, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1116057143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_73
      · exact prime_thirtyEightAJ_1021
      · exact prime_thirtyEightAJ_7487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1116057143) ^ 558028571 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1116057143) ^ 15288454 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1116057143) ^ 1093102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1116057143) ^ 149066 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1189299689 : Nat.Prime 1189299689 := by
  apply lucas_primality 1189299689 (3 : ZMod 1189299689)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (113, 1), (1315597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (113, 1), (1315597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1189299689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_113
      · exact prime_thirtyEightAJ_1315597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1189299689) ^ 594649844 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189299689) ^ 10524776 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189299689) ^ 904 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_113
      · exact prime_thirtyEightAJ_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1295310031 : Nat.Prime 1295310031 := by
  apply lucas_primality 1295310031 (3 : ZMod 1295310031)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (6168143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (6168143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295310031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_6168143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1295310031) ^ 647655015 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295310031) ^ 431770010 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295310031) ^ 259062006 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295310031) ^ 185044290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295310031) ^ 210 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1337232557 : Nat.Prime 1337232557 := by
  apply lucas_primality 1337232557 (2 : ZMod 1337232557)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (769, 1), (39521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (769, 1), (39521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1337232557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_769
      · exact prime_thirtyEightAJ_39521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1337232557) ^ 668616278 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337232557) ^ 121566596 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337232557) ^ 1738924 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337232557) ^ 33836 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1581055589 : Nat.Prime 1581055589 := by
  apply lucas_primality 1581055589 (2 : ZMod 1581055589)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (2971909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (2971909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1581055589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_2971909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1581055589) ^ 790527794 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581055589) ^ 225865084 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581055589) ^ 83213452 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581055589) ^ 532 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1631881507 : Nat.Prime 1631881507 := by
  apply lucas_primality 1631881507 (5 : ZMod 1631881507)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (269, 1), (1011079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (269, 1), (1011079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631881507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_269
      · exact prime_thirtyEightAJ_1011079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1631881507) ^ 815940753 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1631881507) ^ 543960502 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1631881507) ^ 6066474 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1631881507) ^ 1614 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1905970331 : Nat.Prime 1905970331 := by
  apply lucas_primality 1905970331 (2 : ZMod 1905970331)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17327003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17327003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1905970331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_17327003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1905970331) ^ 952985165 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1905970331) ^ 381194066 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1905970331) ^ 173270030 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1905970331) ^ 110 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2042655739 : Nat.Prime 2042655739 := by
  apply lucas_primality 2042655739 (2 : ZMod 2042655739)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11551, 1), (29473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11551, 1), (29473, 1)] : List FactorBlock).map factorBlockValue).prod) = 2042655739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11551
      · exact prime_thirtyEightAJ_29473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2042655739) ^ 1021327869 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2042655739) ^ 680885246 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2042655739) ^ 176838 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2042655739) ^ 69306 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2194301581 : Nat.Prime 2194301581 := by
  apply lucas_primality 2194301581 (2 : ZMod 2194301581)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (36571693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (36571693, 1)] : List FactorBlock).map factorBlockValue).prod) = 2194301581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_36571693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2194301581) ^ 1097150790 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2194301581) ^ 731433860 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2194301581) ^ 438860316 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2194301581) ^ 60 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2754168409 : Nat.Prime 2754168409 := by
  apply lucas_primality 2754168409 (7 : ZMod 2754168409)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (37, 1), (54413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (37, 1), (54413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754168409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_54413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2754168409) ^ 1377084204 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 918056136 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 144956232 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 74436984 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 50616 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3167618777 : Nat.Prime 3167618777 := by
  apply lucas_primality 3167618777 (3 : ZMod 3167618777)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (131, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (131, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3167618777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_131
      · exact prime_thirtyEightAJ_8147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3167618777) ^ 1583809388 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3167618777) ^ 452516968 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3167618777) ^ 59766392 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3167618777) ^ 24180296 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3167618777) ^ 388808 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_4178313463 : Nat.Prime 4178313463 := by
  apply lucas_primality 4178313463 (3 : ZMod 4178313463)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (127, 1), (89891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (127, 1), (89891, 1)] : List FactorBlock).map factorBlockValue).prod) = 4178313463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_61
      · exact prime_thirtyEightAJ_127
      · exact prime_thirtyEightAJ_89891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4178313463) ^ 2089156731 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4178313463) ^ 1392771154 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4178313463) ^ 68496942 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4178313463) ^ 32900106 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4178313463) ^ 46482 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_4536589979 : Nat.Prime 4536589979 := by
  apply lucas_primality 4536589979 (2 : ZMod 4536589979)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1279, 1), (104323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1279, 1), (104323, 1)] : List FactorBlock).map factorBlockValue).prod) = 4536589979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_1279
      · exact prime_thirtyEightAJ_104323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4536589979) ^ 2268294989 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4536589979) ^ 266858234 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4536589979) ^ 3546982 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4536589979) ^ 43486 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_4707646133 : Nat.Prime 4707646133 := by
  apply lucas_primality 4707646133 (2 : ZMod 4707646133)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2887, 1), (58237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2887, 1), (58237, 1)] : List FactorBlock).map factorBlockValue).prod) = 4707646133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_2887
      · exact prime_thirtyEightAJ_58237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4707646133) ^ 2353823066 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4707646133) ^ 672520876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4707646133) ^ 1630636 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4707646133) ^ 80836 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_5599231751 : Nat.Prime 5599231751 := by
  apply lucas_primality 5599231751 (7 : ZMod 5599231751)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (3199561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (3199561, 1)] : List FactorBlock).map factorBlockValue).prod) = 5599231751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_3199561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5599231751) ^ 2799615875 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 5599231751) ^ 1119846350 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 5599231751) ^ 799890250 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 5599231751) ^ 1750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_6312998353 : Nat.Prime 6312998353 := by
  apply lucas_primality 6312998353 (5 : ZMod 6312998353)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (1962997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (1962997, 1)] : List FactorBlock).map factorBlockValue).prod) = 6312998353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_1962997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6312998353) ^ 3156499176 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6312998353) ^ 2104332784 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6312998353) ^ 94223856 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6312998353) ^ 3216 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_6420810587 : Nat.Prime 6420810587 := by
  apply lucas_primality 6420810587 (2 : ZMod 6420810587)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39047, 1), (82219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39047, 1), (82219, 1)] : List FactorBlock).map factorBlockValue).prod) = 6420810587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_39047
      · exact prime_thirtyEightAJ_82219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6420810587) ^ 3210405293 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6420810587) ^ 164438 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6420810587) ^ 78094 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_6696342859 : Nat.Prime 6696342859 := by
  apply lucas_primality 6696342859 (3 : ZMod 6696342859)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1116057143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1116057143, 1)] : List FactorBlock).map factorBlockValue).prod) = 6696342859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_1116057143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6696342859) ^ 3348171429 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6696342859) ^ 2232114286 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6696342859) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7016656643 : Nat.Prime 7016656643 := by
  apply lucas_primality 7016656643 (2 : ZMod 7016656643)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (9718361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (9718361, 1)] : List FactorBlock).map factorBlockValue).prod) = 7016656643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_9718361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7016656643) ^ 3508328321 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7016656643) ^ 369297718 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7016656643) ^ 722 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7204737367 : Nat.Prime 7204737367 := by
  apply lucas_primality 7204737367 (3 : ZMod 7204737367)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (400263187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (400263187, 1)] : List FactorBlock).map factorBlockValue).prod) = 7204737367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_400263187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7204737367) ^ 3602368683 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7204737367) ^ 2401579122 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7204737367) ^ 18 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7524292513 : Nat.Prime 7524292513 := by
  apply lucas_primality 7524292513 (5 : ZMod 7524292513)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (7125277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (7125277, 1)] : List FactorBlock).map factorBlockValue).prod) = 7524292513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_7125277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7524292513) ^ 3762146256 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524292513) ^ 2508097504 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524292513) ^ 684026592 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524292513) ^ 1056 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7669364051 : Nat.Prime 7669364051 := by
  apply lucas_primality 7669364051 (2 : ZMod 7669364051)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (153387281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (153387281, 1)] : List FactorBlock).map factorBlockValue).prod) = 7669364051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_153387281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7669364051) ^ 3834682025 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7669364051) ^ 1533872810 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7669364051) ^ 50 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_8108051443 : Nat.Prime 8108051443 := by
  apply lucas_primality 8108051443 (3 : ZMod 8108051443)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8627, 1), (156641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8627, 1), (156641, 1)] : List FactorBlock).map factorBlockValue).prod) = 8108051443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_8627
      · exact prime_thirtyEightAJ_156641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8108051443) ^ 4054025721 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8108051443) ^ 2702683814 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8108051443) ^ 939846 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8108051443) ^ 51762 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_9340143089 : Nat.Prime 9340143089 := by
  apply lucas_primality 9340143089 (3 : ZMod 9340143089)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (14238023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (14238023, 1)] : List FactorBlock).map factorBlockValue).prod) = 9340143089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_14238023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9340143089) ^ 4670071544 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9340143089) ^ 227808368 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9340143089) ^ 656 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_9738312517 : Nat.Prime 9738312517 := by
  apply lucas_primality 9738312517 (11 : ZMod 9738312517)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (23, 1), (67, 1), (9239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (23, 1), (67, 1), (9239, 1)] : List FactorBlock).map factorBlockValue).prod) = 9738312517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_9239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9738312517) ^ 4869156258 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 9738312517) ^ 3246104172 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 9738312517) ^ 512542764 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 9738312517) ^ 423404892 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 9738312517) ^ 145347948 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 9738312517) ^ 1054044 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_9955301119 : Nat.Prime 9955301119 := by
  apply lucas_primality 9955301119 (15 : ZMod 9955301119)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1051, 1), (225529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1051, 1), (225529, 1)] : List FactorBlock).map factorBlockValue).prod) = 9955301119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_1051
      · exact prime_thirtyEightAJ_225529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 9955301119) ^ 4977650559 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 3318433706 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 1422185874 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 9472218 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 44142 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_10143596371 : Nat.Prime 10143596371 := by
  apply lucas_primality 10143596371 (2 : ZMod 10143596371)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (7863253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (7863253, 1)] : List FactorBlock).map factorBlockValue).prod) = 10143596371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_7863253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10143596371) ^ 5071798185 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 3381198790 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 2028719274 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 235897590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 1290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_10345142371 : Nat.Prime 10345142371 := by
  apply lucas_primality 10345142371 (3 : ZMod 10345142371)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (67, 1), (166027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (67, 1), (166027, 1)] : List FactorBlock).map factorBlockValue).prod) = 10345142371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_166027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10345142371) ^ 5172571185 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10345142371) ^ 3448380790 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10345142371) ^ 2069028474 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10345142371) ^ 333714270 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10345142371) ^ 154405110 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10345142371) ^ 62310 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_10924824187 : Nat.Prime 10924824187 := by
  apply lucas_primality 10924824187 (2 : ZMod 10924824187)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (199, 1), (1016641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (199, 1), (1016641, 1)] : List FactorBlock).map factorBlockValue).prod) = 10924824187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_199
      · exact prime_thirtyEightAJ_1016641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10924824187) ^ 5462412093 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10924824187) ^ 3641608062 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10924824187) ^ 54898614 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10924824187) ^ 10746 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_12831738653 : Nat.Prime 12831738653 := by
  apply lucas_primality 12831738653 (2 : ZMod 12831738653)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (47, 1), (4014937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (47, 1), (4014937, 1)] : List FactorBlock).map factorBlockValue).prod) = 12831738653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_4014937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12831738653) ^ 6415869326 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831738653) ^ 754808156 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831738653) ^ 273015716 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831738653) ^ 3196 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_17369393617 : Nat.Prime 17369393617 := by
  apply lucas_primality 17369393617 (5 : ZMod 17369393617)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (367, 1), (328667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (367, 1), (328667, 1)] : List FactorBlock).map factorBlockValue).prod) = 17369393617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_367
      · exact prime_thirtyEightAJ_328667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17369393617) ^ 8684696808 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17369393617) ^ 5789797872 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17369393617) ^ 47328048 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17369393617) ^ 52848 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_17404397201 : Nat.Prime 17404397201 := by
  apply lucas_primality 17404397201 (6 : ZMod 17404397201)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (73, 1), (577, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (73, 1), (577, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 17404397201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_73
      · exact prime_thirtyEightAJ_577
      · exact prime_thirtyEightAJ_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17404397201) ^ 8702198600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 3480879440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 238416400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 30163600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 16848400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_17671339223 : Nat.Prime 17671339223 := by
  apply lucas_primality 17671339223 (5 : ZMod 17671339223)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4093, 1), (2158727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4093, 1), (2158727, 1)] : List FactorBlock).map factorBlockValue).prod) = 17671339223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_4093
      · exact prime_thirtyEightAJ_2158727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17671339223) ^ 8835669611 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17671339223) ^ 4317454 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17671339223) ^ 8186 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_18201107173 : Nat.Prime 18201107173 := by
  apply lucas_primality 18201107173 (2 : ZMod 18201107173)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (22638193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (22638193, 1)] : List FactorBlock).map factorBlockValue).prod) = 18201107173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_22638193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18201107173) ^ 9100553586 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18201107173) ^ 6067035724 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18201107173) ^ 271658316 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18201107173) ^ 804 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_19678817629 : Nat.Prime 19678817629 := by
  apply lucas_primality 19678817629 (2 : ZMod 19678817629)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (546633823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (546633823, 1)] : List FactorBlock).map factorBlockValue).prod) = 19678817629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_546633823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19678817629) ^ 9839408814 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19678817629) ^ 6559605876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19678817629) ^ 36 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_20426557391 : Nat.Prime 20426557391 := by
  apply lucas_primality 20426557391 (11 : ZMod 20426557391)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2042655739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2042655739, 1)] : List FactorBlock).map factorBlockValue).prod) = 20426557391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_2042655739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 20426557391) ^ 10213278695 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 20426557391) ^ 4085311478 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 20426557391) ^ 10 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_23861595971 : Nat.Prime 23861595971 := by
  apply lucas_primality 23861595971 (2 : ZMod 23861595971)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (40443383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (40443383, 1)] : List FactorBlock).map factorBlockValue).prod) = 23861595971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_40443383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23861595971) ^ 11930797985 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23861595971) ^ 4772319194 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23861595971) ^ 404433830 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23861595971) ^ 590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_25121561411 : Nat.Prime 25121561411 := by
  apply lucas_primality 25121561411 (6 : ZMod 25121561411)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (41, 1), (506381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (41, 1), (506381, 1)] : List FactorBlock).map factorBlockValue).prod) = 25121561411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_506381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 25121561411) ^ 12560780705 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 5024312282 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 2283778310 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 612721010 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 49610 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_25340904301 : Nat.Prime 25340904301 := by
  apply lucas_primality 25340904301 (2 : ZMod 25340904301)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (83, 1), (839, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (83, 1), (839, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 25340904301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_83
      · exact prime_thirtyEightAJ_839
      · exact prime_thirtyEightAJ_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25340904301) ^ 12670452150 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 8446968100 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 5068180860 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 305312100 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 30203700 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 20891100 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_29344639003 : Nat.Prime 29344639003 := by
  apply lucas_primality 29344639003 (2 : ZMod 29344639003)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (571, 1), (23087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (571, 1), (23087, 1)] : List FactorBlock).map factorBlockValue).prod) = 29344639003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_571
      · exact prime_thirtyEightAJ_23087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29344639003) ^ 14672319501 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29344639003) ^ 9781546334 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29344639003) ^ 4192091286 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29344639003) ^ 553672434 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29344639003) ^ 51391662 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29344639003) ^ 1271046 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_30223402003 : Nat.Prime 30223402003 := by
  apply lucas_primality 30223402003 (3 : ZMod 30223402003)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (257, 1), (151939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (257, 1), (151939, 1)] : List FactorBlock).map factorBlockValue).prod) = 30223402003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_257
      · exact prime_thirtyEightAJ_151939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30223402003) ^ 15111701001 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30223402003) ^ 10074467334 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30223402003) ^ 702869814 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30223402003) ^ 117600786 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30223402003) ^ 198918 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_32318626891 : Nat.Prime 32318626891 := by
  apply lucas_primality 32318626891 (2 : ZMod 32318626891)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (29, 1), (337, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (29, 1), (337, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 32318626891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_337
      · exact prime_thirtyEightAJ_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32318626891) ^ 16159313445 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 10772875630 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 6463725378 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 2938056990 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 1114435410 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 95900970 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 35475990 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_151
      · exact prime_thirtyEightAJ_479
      · exact prime_thirtyEightAJ_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_45367371463 : Nat.Prime 45367371463 := by
  apply lucas_primality 45367371463 (6 : ZMod 45367371463)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1080175511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1080175511, 1)] : List FactorBlock).map factorBlockValue).prod) = 45367371463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_1080175511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 45367371463) ^ 22683685731 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45367371463) ^ 15122457154 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45367371463) ^ 6481053066 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45367371463) ^ 42 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_50180173151 : Nat.Prime 50180173151 := by
  apply lucas_primality 50180173151 (11 : ZMod 50180173151)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (233, 1), (347, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (233, 1), (347, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) = 50180173151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_233
      · exact prime_thirtyEightAJ_347
      · exact prime_thirtyEightAJ_12413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 50180173151) ^ 25090086575 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 50180173151) ^ 10036034630 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 50180173151) ^ 215365550 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 50180173151) ^ 144611450 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 50180173151) ^ 4042550 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_51862708169 : Nat.Prime 51862708169 := by
  apply lucas_primality 51862708169 (3 : ZMod 51862708169)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (443, 1), (248033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (443, 1), (248033, 1)] : List FactorBlock).map factorBlockValue).prod) = 51862708169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_443
      · exact prime_thirtyEightAJ_248033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51862708169) ^ 25931354084 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51862708169) ^ 879028952 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51862708169) ^ 117071576 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51862708169) ^ 209096 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_52600248139 : Nat.Prime 52600248139 := by
  apply lucas_primality 52600248139 (2 : ZMod 52600248139)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (282797033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (282797033, 1)] : List FactorBlock).map factorBlockValue).prod) = 52600248139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_282797033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52600248139) ^ 26300124069 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600248139) ^ 17533416046 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600248139) ^ 1696782198 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600248139) ^ 186 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_57451848793 : Nat.Prime 57451848793 := by
  apply lucas_primality 57451848793 (5 : ZMod 57451848793)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 3), (389, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 3), (389, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) = 57451848793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_389
      · exact prime_thirtyEightAJ_2801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57451848793) ^ 28725924396 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 19150616264 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 4419372984 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 147691128 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 20511192 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_58384288267 : Nat.Prime 58384288267 := by
  apply lucas_primality 58384288267 (2 : ZMod 58384288267)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (373, 1), (379, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (373, 1), (379, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 58384288267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_373
      · exact prime_thirtyEightAJ_379
      · exact prime_thirtyEightAJ_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58384288267) ^ 29192144133 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 19461429422 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 3434369898 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 156526242 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 154048254 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 14419434 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_82893039373 : Nat.Prime 82893039373 := by
  apply lucas_primality 82893039373 (6 : ZMod 82893039373)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (13, 1), (29, 1), (31, 1), (17911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (13, 1), (29, 1), (31, 1), (17911, 1)] : List FactorBlock).map factorBlockValue).prod) = 82893039373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_17911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 82893039373) ^ 41446519686 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 82893039373) ^ 27631013124 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 82893039373) ^ 7535730852 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 82893039373) ^ 6376387644 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 82893039373) ^ 2858380668 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 82893039373) ^ 2673969012 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 82893039373) ^ 4628052 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_94167868097 : Nat.Prime 94167868097 := by
  apply lucas_primality 94167868097 (3 : ZMod 94167868097)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (1163, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (1163, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) = 94167868097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_1163
      · exact prime_thirtyEightAJ_66587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 94167868097) ^ 47083934048 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 94167868097) ^ 4956203584 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 94167868097) ^ 80969792 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 94167868097) ^ 1414208 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_109926847451 : Nat.Prime 109926847451 := by
  apply lucas_primality 109926847451 (6 : ZMod 109926847451)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (19, 1), (23, 1), (102673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (19, 1), (23, 1), (102673, 1)] : List FactorBlock).map factorBlockValue).prod) = 109926847451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_102673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109926847451) ^ 54963423725 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 21985369490 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 15703835350 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 5785623550 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 4779428150 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 1070650 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_112971088693 : Nat.Prime 112971088693 := by
  apply lucas_primality 112971088693 (6 : ZMod 112971088693)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (1609, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (1609, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 112971088693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_1609
      · exact prime_thirtyEightAJ_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 112971088693) ^ 56485544346 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 37657029564 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 16138726956 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 10270098972 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 70211988 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 13380444 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_119645280401 : Nat.Prime 119645280401 := by
  apply lucas_primality 119645280401 (6 : ZMod 119645280401)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (299113201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (299113201, 1)] : List FactorBlock).map factorBlockValue).prod) = 119645280401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_299113201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 119645280401) ^ 59822640200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 119645280401) ^ 23929056080 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 119645280401) ^ 400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_120893608013 : Nat.Prime 120893608013 := by
  apply lucas_primality 120893608013 (2 : ZMod 120893608013)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (30223402003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (30223402003, 1)] : List FactorBlock).map factorBlockValue).prod) = 120893608013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_30223402003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 120893608013) ^ 60446804006 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 120893608013) ^ 4 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_177204535801 : Nat.Prime 177204535801 := by
  apply lucas_primality 177204535801 (11 : ZMod 177204535801)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (89, 1), (1451, 1), (2287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (89, 1), (1451, 1), (2287, 1)] : List FactorBlock).map factorBlockValue).prod) = 177204535801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_89
      · exact prime_thirtyEightAJ_1451
      · exact prime_thirtyEightAJ_2287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 177204535801) ^ 88602267900 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 59068178600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 35440907160 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 1991062200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 122125800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 77483400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_177402750137 : Nat.Prime 177402750137 := by
  apply lucas_primality 177402750137 (3 : ZMod 177402750137)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (515705669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (515705669, 1)] : List FactorBlock).map factorBlockValue).prod) = 177402750137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_515705669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 177402750137) ^ 88701375068 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 177402750137) ^ 4125645352 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 177402750137) ^ 344 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_199557398321 : Nat.Prime 199557398321 := by
  apply lucas_primality 199557398321 (3 : ZMod 199557398321)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (356352497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (356352497, 1)] : List FactorBlock).map factorBlockValue).prod) = 199557398321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_356352497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 199557398321) ^ 99778699160 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 199557398321) ^ 39911479664 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 199557398321) ^ 28508199760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 199557398321) ^ 560 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_223818761263 : Nat.Prime 223818761263 := by
  apply lucas_primality 223818761263 (3 : ZMod 223818761263)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (2194301581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (2194301581, 1)] : List FactorBlock).map factorBlockValue).prod) = 223818761263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_2194301581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 223818761263) ^ 111909380631 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 223818761263) ^ 74606253754 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 223818761263) ^ 13165809486 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 223818761263) ^ 102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_238746470311 : Nat.Prime 238746470311 := by
  apply lucas_primality 238746470311 (13 : ZMod 238746470311)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (109, 1), (24337051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (109, 1), (24337051, 1)] : List FactorBlock).map factorBlockValue).prod) = 238746470311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_109
      · exact prime_thirtyEightAJ_24337051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 238746470311) ^ 119373235155 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 79582156770 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 47749294062 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 2190334590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 9810 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_256488670019 : Nat.Prime 256488670019 := by
  apply lucas_primality 256488670019 (2 : ZMod 256488670019)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (107, 1), (171220741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (107, 1), (171220741, 1)] : List FactorBlock).map factorBlockValue).prod) = 256488670019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_107
      · exact prime_thirtyEightAJ_171220741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 256488670019) ^ 128244335009 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256488670019) ^ 36641238574 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256488670019) ^ 2397090374 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256488670019) ^ 1498 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_300382866011 : Nat.Prime 300382866011 := by
  apply lucas_primality 300382866011 (2 : ZMod 300382866011)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9439, 1), (3182359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9439, 1), (3182359, 1)] : List FactorBlock).map factorBlockValue).prod) = 300382866011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_9439
      · exact prime_thirtyEightAJ_3182359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 300382866011) ^ 150191433005 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 300382866011) ^ 60076573202 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 300382866011) ^ 31823590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 300382866011) ^ 94390 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_404430377963 : Nat.Prime 404430377963 := by
  apply lucas_primality 404430377963 (2 : ZMod 404430377963)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2887, 1), (5387951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2887, 1), (5387951, 1)] : List FactorBlock).map factorBlockValue).prod) = 404430377963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_2887
      · exact prime_thirtyEightAJ_5387951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 404430377963) ^ 202215188981 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 404430377963) ^ 31110029074 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 404430377963) ^ 140086726 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 404430377963) ^ 75062 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_451884354773 : Nat.Prime 451884354773 := by
  apply lucas_primality 451884354773 (2 : ZMod 451884354773)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (112971088693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (112971088693, 1)] : List FactorBlock).map factorBlockValue).prod) = 451884354773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_112971088693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 451884354773) ^ 225942177386 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 451884354773) ^ 4 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_457432879441 : Nat.Prime 457432879441 := by
  apply lucas_primality 457432879441 (7 : ZMod 457432879441)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1905970331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1905970331, 1)] : List FactorBlock).map factorBlockValue).prod) = 457432879441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_1905970331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 457432879441) ^ 228716439720 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 457432879441) ^ 152477626480 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 457432879441) ^ 91486575888 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 457432879441) ^ 240 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_397
      · exact prime_thirtyEightAJ_2531
      · exact prime_thirtyEightAJ_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_470381570423 : Nat.Prime 470381570423 := by
  apply lucas_primality 470381570423 (5 : ZMod 470381570423)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1559, 1), (150860029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1559, 1), (150860029, 1)] : List FactorBlock).map factorBlockValue).prod) = 470381570423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_1559
      · exact prime_thirtyEightAJ_150860029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 470381570423) ^ 235190785211 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 470381570423) ^ 301720058 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 470381570423) ^ 3118 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_502541912603 : Nat.Prime 502541912603 := by
  apply lucas_primality 502541912603 (2 : ZMod 502541912603)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (10924824187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (10924824187, 1)] : List FactorBlock).map factorBlockValue).prod) = 502541912603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_10924824187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 502541912603) ^ 251270956301 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 502541912603) ^ 21849648374 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 502541912603) ^ 46 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_521527561367 : Nat.Prime 521527561367 := by
  apply lucas_primality 521527561367 (5 : ZMod 521527561367)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (271, 1), (3881, 1), (35419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (271, 1), (3881, 1), (35419, 1)] : List FactorBlock).map factorBlockValue).prod) = 521527561367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_271
      · exact prime_thirtyEightAJ_3881
      · exact prime_thirtyEightAJ_35419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 521527561367) ^ 260763780683 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 521527561367) ^ 74503937338 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 521527561367) ^ 1924455946 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 521527561367) ^ 134379686 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 521527561367) ^ 14724514 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_622352498029 : Nat.Prime 622352498029 := by
  apply lucas_primality 622352498029 (2 : ZMod 622352498029)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (51862708169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (51862708169, 1)] : List FactorBlock).map factorBlockValue).prod) = 622352498029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_51862708169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 622352498029) ^ 311176249014 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 622352498029) ^ 207450832676 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 622352498029) ^ 12 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1065502430449 : Nat.Prime 1065502430449 := by
  apply lucas_primality 1065502430449 (11 : ZMod 1065502430449)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (283, 1), (78438047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (283, 1), (78438047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065502430449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_283
      · exact prime_thirtyEightAJ_78438047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1065502430449) ^ 532751215224 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1065502430449) ^ 355167476816 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1065502430449) ^ 3765026256 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1065502430449) ^ 13584 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1163890027141 : Nat.Prime 1163890027141 := by
  apply lucas_primality 1163890027141 (6 : ZMod 1163890027141)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (2843, 1), (184409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (2843, 1), (184409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1163890027141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_2843
      · exact prime_thirtyEightAJ_184409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1163890027141) ^ 581945013570 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1163890027141) ^ 387963342380 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1163890027141) ^ 232778005428 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1163890027141) ^ 31456487220 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1163890027141) ^ 409387980 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1163890027141) ^ 6311460 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_35279
      · exact prime_thirtyEightAJ_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1887439493743 : Nat.Prime 1887439493743 := by
  apply lucas_primality 1887439493743 (6 : ZMod 1887439493743)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (857, 1), (3033581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (857, 1), (3033581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1887439493743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_857
      · exact prime_thirtyEightAJ_3033581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1887439493743) ^ 943719746871 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1887439493743) ^ 629146497914 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1887439493743) ^ 171585408522 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1887439493743) ^ 2202379806 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1887439493743) ^ 622182 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2079119063237 : Nat.Prime 2079119063237 := by
  apply lucas_primality 2079119063237 (2 : ZMod 2079119063237)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139939, 1), (3714331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139939, 1), (3714331, 1)] : List FactorBlock).map factorBlockValue).prod) = 2079119063237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_139939
      · exact prime_thirtyEightAJ_3714331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2079119063237) ^ 1039559531618 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2079119063237) ^ 14857324 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2079119063237) ^ 559756 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2432604289021 : Nat.Prime 2432604289021 := by
  apply lucas_primality 2432604289021 (2 : ZMod 2432604289021)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (8969, 1), (4520393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (8969, 1), (4520393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2432604289021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_8969
      · exact prime_thirtyEightAJ_4520393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2432604289021) ^ 1216302144510 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432604289021) ^ 810868096340 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432604289021) ^ 486520857804 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432604289021) ^ 271223580 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432604289021) ^ 538140 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2625789748187 : Nat.Prime 2625789748187 := by
  apply lucas_primality 2625789748187 (2 : ZMod 2625789748187)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (241, 1), (495245143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (241, 1), (495245143, 1)] : List FactorBlock).map factorBlockValue).prod) = 2625789748187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_241
      · exact prime_thirtyEightAJ_495245143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2625789748187) ^ 1312894874093 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2625789748187) ^ 238708158926 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2625789748187) ^ 10895393146 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2625789748187) ^ 5302 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3097034815909 : Nat.Prime 3097034815909 := by
  apply lucas_primality 3097034815909 (13 : ZMod 3097034815909)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (30689, 1), (764521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (30689, 1), (764521, 1)] : List FactorBlock).map factorBlockValue).prod) = 3097034815909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_30689
      · exact prime_thirtyEightAJ_764521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3097034815909) ^ 1548517407954 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3097034815909) ^ 1032344938636 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3097034815909) ^ 281548619628 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3097034815909) ^ 100916772 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3097034815909) ^ 4050948 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3218300677433 : Nat.Prime 3218300677433 := by
  apply lucas_primality 3218300677433 (3 : ZMod 3218300677433)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (3167618777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (3167618777, 1)] : List FactorBlock).map factorBlockValue).prod) = 3218300677433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_127
      · exact prime_thirtyEightAJ_3167618777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3218300677433) ^ 1609150338716 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3218300677433) ^ 25340950216 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3218300677433) ^ 1016 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3327754464481 : Nat.Prime 3327754464481 := by
  apply lucas_primality 3327754464481 (13 : ZMod 3327754464481)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (167, 1), (223, 1), (186161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (167, 1), (223, 1), (186161, 1)] : List FactorBlock).map factorBlockValue).prod) = 3327754464481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_167
      · exact prime_thirtyEightAJ_223
      · exact prime_thirtyEightAJ_186161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3327754464481) ^ 1663877232240 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3327754464481) ^ 1109251488160 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3327754464481) ^ 665550892896 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3327754464481) ^ 19926673440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3327754464481) ^ 14922665760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3327754464481) ^ 17875680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_5802512756111 : Nat.Prime 5802512756111 := by
  apply lucas_primality 5802512756111 (11 : ZMod 5802512756111)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (82893039373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (82893039373, 1)] : List FactorBlock).map factorBlockValue).prod) = 5802512756111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_82893039373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5802512756111) ^ 2901256378055 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5802512756111) ^ 1160502551222 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5802512756111) ^ 828930393730 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5802512756111) ^ 70 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_6147094629469 : Nat.Prime 6147094629469 := by
  apply lucas_primality 6147094629469 (2 : ZMod 6147094629469)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (8521, 1), (4624393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (8521, 1), (4624393, 1)] : List FactorBlock).map factorBlockValue).prod) = 6147094629469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_8521
      · exact prime_thirtyEightAJ_4624393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6147094629469) ^ 3073547314734 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 2049031543156 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 472853433036 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 721405308 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 1329276 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_6684901168709 : Nat.Prime 6684901168709 := by
  apply lucas_primality 6684901168709 (2 : ZMod 6684901168709)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (238746470311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (238746470311, 1)] : List FactorBlock).map factorBlockValue).prod) = 6684901168709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_238746470311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6684901168709) ^ 3342450584354 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6684901168709) ^ 954985881244 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6684901168709) ^ 28 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7183927164917 : Nat.Prime 7183927164917 := by
  apply lucas_primality 7183927164917 (2 : ZMod 7183927164917)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (257, 1), (277, 1), (181499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (257, 1), (277, 1), (181499, 1)] : List FactorBlock).map factorBlockValue).prod) = 7183927164917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_139
      · exact prime_thirtyEightAJ_257
      · exact prime_thirtyEightAJ_277
      · exact prime_thirtyEightAJ_181499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7183927164917) ^ 3591963582458 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7183927164917) ^ 51682929244 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7183927164917) ^ 27953023988 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7183927164917) ^ 25934755108 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7183927164917) ^ 39581084 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7296851506151 : Nat.Prime 7296851506151 := by
  apply lucas_primality 7296851506151 (7 : ZMod 7296851506151)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (4707646133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (4707646133, 1)] : List FactorBlock).map factorBlockValue).prod) = 7296851506151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_4707646133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7296851506151) ^ 3648425753075 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 7296851506151) ^ 1459370301230 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 7296851506151) ^ 235382306650 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 7296851506151) ^ 1550 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_9231510145621 : Nat.Prime 9231510145621 := by
  apply lucas_primality 9231510145621 (2 : ZMod 9231510145621)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (59629, 1), (368609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (59629, 1), (368609, 1)] : List FactorBlock).map factorBlockValue).prod) = 9231510145621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_59629
      · exact prime_thirtyEightAJ_368609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9231510145621) ^ 4615755072810 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 3077170048540 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 1846302029124 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 1318787163660 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 154815780 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 25044180 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_13706876732477 : Nat.Prime 13706876732477 := by
  apply lucas_primality 13706876732477 (2 : ZMod 13706876732477)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1259, 1), (3821, 1), (712321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1259, 1), (3821, 1), (712321, 1)] : List FactorBlock).map factorBlockValue).prod) = 13706876732477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_1259
      · exact prime_thirtyEightAJ_3821
      · exact prime_thirtyEightAJ_712321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13706876732477) ^ 6853438366238 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13706876732477) ^ 10887114164 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13706876732477) ^ 3587248556 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13706876732477) ^ 19242556 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_19309804064599 : Nat.Prime 19309804064599 := by
  apply lucas_primality 19309804064599 (11 : ZMod 19309804064599)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3218300677433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3218300677433, 1)] : List FactorBlock).map factorBlockValue).prod) = 19309804064599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_3218300677433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 19309804064599) ^ 9654902032299 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 19309804064599) ^ 6436601354866 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 19309804064599) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_21415214170873 : Nat.Prime 21415214170873 := by
  apply lucas_primality 21415214170873 (7 : ZMod 21415214170873)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2293, 1), (129713707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2293, 1), (129713707, 1)] : List FactorBlock).map factorBlockValue).prod) = 21415214170873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_2293
      · exact prime_thirtyEightAJ_129713707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 21415214170873) ^ 10707607085436 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21415214170873) ^ 7138404723624 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21415214170873) ^ 9339386904 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21415214170873) ^ 165096 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_24403220915303 : Nat.Prime 24403220915303 := by
  apply lucas_primality 24403220915303 (5 : ZMod 24403220915303)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1497407, 1), (8148493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1497407, 1), (8148493, 1)] : List FactorBlock).map factorBlockValue).prod) = 24403220915303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_1497407
      · exact prime_thirtyEightAJ_8148493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24403220915303) ^ 12201610457651 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 24403220915303) ^ 16296986 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 24403220915303) ^ 2994814 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_26561252249023 : Nat.Prime 26561252249023 := by
  apply lucas_primality 26561252249023 (3 : ZMod 26561252249023)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (119645280401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (119645280401, 1)] : List FactorBlock).map factorBlockValue).prod) = 26561252249023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_119645280401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26561252249023) ^ 13280626124511 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26561252249023) ^ 8853750749674 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26561252249023) ^ 717871682406 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26561252249023) ^ 222 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_28576857822509 : Nat.Prime 28576857822509 := by
  apply lucas_primality 28576857822509 (2 : ZMod 28576857822509)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (239, 1), (1663, 1), (131203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (239, 1), (1663, 1), (131203, 1)] : List FactorBlock).map factorBlockValue).prod) = 28576857822509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_137
      · exact prime_thirtyEightAJ_239
      · exact prime_thirtyEightAJ_1663
      · exact prime_thirtyEightAJ_131203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28576857822509) ^ 14288428911254 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 208590203084 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 119568442772 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 17183919316 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 217806436 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_34440719883793 : Nat.Prime 34440719883793 := by
  apply lucas_primality 34440719883793 (10 : ZMod 34440719883793)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (2621, 1), (14408221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (2621, 1), (14408221, 1)] : List FactorBlock).map factorBlockValue).prod) = 34440719883793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_2621
      · exact prime_thirtyEightAJ_14408221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 34440719883793) ^ 17220359941896 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 11480239961264 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 1812669467568 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 13140297552 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 2390352 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_34880267703949 : Nat.Prime 34880267703949 := by
  apply lucas_primality 34880267703949 (2 : ZMod 34880267703949)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (379, 1), (7669364051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (379, 1), (7669364051, 1)] : List FactorBlock).map factorBlockValue).prod) = 34880267703949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_379
      · exact prime_thirtyEightAJ_7669364051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34880267703949) ^ 17440133851974 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34880267703949) ^ 11626755901316 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34880267703949) ^ 92032368612 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34880267703949) ^ 4548 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_36489473195519 : Nat.Prime 36489473195519 := by
  apply lucas_primality 36489473195519 (7 : ZMod 36489473195519)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (93169, 1), (27974873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (93169, 1), (27974873, 1)] : List FactorBlock).map factorBlockValue).prod) = 36489473195519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_93169
      · exact prime_thirtyEightAJ_27974873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36489473195519) ^ 18244736597759 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 36489473195519) ^ 5212781885074 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 36489473195519) ^ 391648222 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 36489473195519) ^ 1304366 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_40721844524131 : Nat.Prime 40721844524131 := by
  apply lucas_primality 40721844524131 (3 : ZMod 40721844524131)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1), (311, 1), (821497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1), (311, 1), (821497, 1)] : List FactorBlock).map factorBlockValue).prod) = 40721844524131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_311
      · exact prime_thirtyEightAJ_821497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40721844524131) ^ 20360922262065 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 13573948174710 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 8144368904826 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 5817406360590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 3701985865830 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 1770514979310 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 130938406830 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40721844524131) ^ 49570290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_44321647017829 : Nat.Prime 44321647017829 := by
  apply lucas_primality 44321647017829 (2 : ZMod 44321647017829)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (154061, 1), (23974079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (154061, 1), (23974079, 1)] : List FactorBlock).map factorBlockValue).prod) = 44321647017829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_154061
      · exact prime_thirtyEightAJ_23974079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44321647017829) ^ 22160823508914 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44321647017829) ^ 14773882339276 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44321647017829) ^ 287688948 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44321647017829) ^ 1848732 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_51255046916287 : Nat.Prime 51255046916287 := by
  apply lucas_primality 51255046916287 (3 : ZMod 51255046916287)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (349, 1), (661543237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (349, 1), (661543237, 1)] : List FactorBlock).map factorBlockValue).prod) = 51255046916287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_349
      · exact prime_thirtyEightAJ_661543237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51255046916287) ^ 25627523458143 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51255046916287) ^ 17085015638762 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51255046916287) ^ 1385271538278 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51255046916287) ^ 146862598614 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51255046916287) ^ 77478 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_76294320034637 : Nat.Prime 76294320034637 := by
  apply lucas_primality 76294320034637 (2 : ZMod 76294320034637)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (23, 1), (29, 1), (8387, 1), (18233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (23, 1), (29, 1), (8387, 1), (18233, 1)] : List FactorBlock).map factorBlockValue).prod) = 76294320034637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_8387
      · exact prime_thirtyEightAJ_18233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76294320034637) ^ 38147160017318 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 6935847275876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 4487901178508 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 3317144349332 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 2630838621884 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 9096735428 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 4184408492 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_107293428600521 : Nat.Prime 107293428600521 := by
  apply lucas_primality 107293428600521 (3 : ZMod 107293428600521)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (449, 1), (19489, 1), (306533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (449, 1), (19489, 1), (306533, 1)] : List FactorBlock).map factorBlockValue).prod) = 107293428600521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_449
      · exact prime_thirtyEightAJ_19489
      · exact prime_thirtyEightAJ_306533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107293428600521) ^ 53646714300260 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 21458685720104 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 238960865480 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 5505332680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 350022440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_115121083129651 : Nat.Prime 115121083129651 := by
  apply lucas_primality 115121083129651 (7 : ZMod 115121083129651)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (13, 1), (19678817629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (13, 1), (19678817629, 1)] : List FactorBlock).map factorBlockValue).prod) = 115121083129651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_19678817629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 115121083129651) ^ 57560541564825 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 115121083129651) ^ 38373694376550 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 115121083129651) ^ 23024216625930 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 115121083129651) ^ 8855467933050 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 115121083129651) ^ 5850 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_141598139481229 : Nat.Prime 141598139481229 := by
  apply lucas_primality 141598139481229 (2 : ZMod 141598139481229)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (691, 1), (254872777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (691, 1), (254872777, 1)] : List FactorBlock).map factorBlockValue).prod) = 141598139481229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_691
      · exact prime_thirtyEightAJ_254872777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141598139481229) ^ 70799069740614 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 47199379827076 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 2113405066884 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 204917712708 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 555564 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_176640763490393 : Nat.Prime 176640763490393 := by
  apply lucas_primality 176640763490393 (3 : ZMod 176640763490393)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (137, 1), (743, 1), (11416631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (137, 1), (743, 1), (11416631, 1)] : List FactorBlock).map factorBlockValue).prod) = 176640763490393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_137
      · exact prime_thirtyEightAJ_743
      · exact prime_thirtyEightAJ_11416631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 176640763490393) ^ 88320381745196 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 9296882288968 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 1289348638616 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 237739923944 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 15472232 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_183637428518651 : Nat.Prime 183637428518651 := by
  apply lucas_primality 183637428518651 (7 : ZMod 183637428518651)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (7481, 1), (21345371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (7481, 1), (21345371, 1)] : List FactorBlock).map factorBlockValue).prod) = 183637428518651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_7481
      · exact prime_thirtyEightAJ_21345371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 183637428518651) ^ 91818714259325 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183637428518651) ^ 36727485703730 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183637428518651) ^ 7984236022550 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183637428518651) ^ 24547176650 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183637428518651) ^ 8603150 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_193340264938297 : Nat.Prime 193340264938297 := by
  apply lucas_primality 193340264938297 (10 : ZMod 193340264938297)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2531, 1), (454695737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2531, 1), (454695737, 1)] : List FactorBlock).map factorBlockValue).prod) = 193340264938297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_2531
      · exact prime_thirtyEightAJ_454695737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 193340264938297) ^ 96670132469148 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 64446754979432 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 27620037848328 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 76388883816 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 425208 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_206658187604573 : Nat.Prime 206658187604573 := by
  apply lucas_primality 206658187604573 (2 : ZMod 206658187604573)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (354469, 1), (13250177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (354469, 1), (13250177, 1)] : List FactorBlock).map factorBlockValue).prod) = 206658187604573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_354469
      · exact prime_thirtyEightAJ_13250177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 206658187604573) ^ 103329093802286 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 206658187604573) ^ 18787107964052 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 206658187604573) ^ 583007788 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 206658187604573) ^ 15596636 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_258482284077389 : Nat.Prime 258482284077389 := by
  apply lucas_primality 258482284077389 (2 : ZMod 258482284077389)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (9231510145621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (9231510145621, 1)] : List FactorBlock).map factorBlockValue).prod) = 258482284077389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_9231510145621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 258482284077389) ^ 129241142038694 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 258482284077389) ^ 36926040582484 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 258482284077389) ^ 28 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_344121459783347 : Nat.Prime 344121459783347 := by
  apply lucas_primality 344121459783347 (2 : ZMod 344121459783347)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (311, 1), (9109, 1), (1239523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (311, 1), (9109, 1), (1239523, 1)] : List FactorBlock).map factorBlockValue).prod) = 344121459783347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_311
      · exact prime_thirtyEightAJ_9109
      · exact prime_thirtyEightAJ_1239523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 344121459783347) ^ 172060729891673 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 49160208540478 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 1106499870686 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 37778181994 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 277624102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_631677429336341 : Nat.Prime 631677429336341 := by
  apply lucas_primality 631677429336341 (2 : ZMod 631677429336341)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7559, 1), (4178313463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7559, 1), (4178313463, 1)] : List FactorBlock).map factorBlockValue).prod) = 631677429336341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7559
      · exact prime_thirtyEightAJ_4178313463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 631677429336341) ^ 315838714668170 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 631677429336341) ^ 126335485867268 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 631677429336341) ^ 83566269260 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 631677429336341) ^ 151180 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_650865279863299 : Nat.Prime 650865279863299 := by
  apply lucas_primality 650865279863299 (2 : ZMod 650865279863299)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (317, 1), (17987, 1), (442439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (317, 1), (17987, 1), (442439, 1)] : List FactorBlock).map factorBlockValue).prod) = 650865279863299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_317
      · exact prime_thirtyEightAJ_17987
      · exact prime_thirtyEightAJ_442439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 650865279863299) ^ 325432639931649 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 650865279863299) ^ 216955093287766 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 650865279863299) ^ 15136401857286 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 650865279863299) ^ 2053202775594 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 650865279863299) ^ 36185316054 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 650865279863299) ^ 1471084782 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_744118882849051 : Nat.Prime 744118882849051 := by
  apply lucas_primality 744118882849051 (3 : ZMod 744118882849051)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37813, 1), (131192779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37813, 1), (131192779, 1)] : List FactorBlock).map factorBlockValue).prod) = 744118882849051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_37813
      · exact prime_thirtyEightAJ_131192779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 744118882849051) ^ 372059441424525 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 744118882849051) ^ 248039627616350 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 744118882849051) ^ 148823776569810 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 744118882849051) ^ 19678916850 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 744118882849051) ^ 5671950 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_823331149041853 : Nat.Prime 823331149041853 := by
  apply lucas_primality 823331149041853 (2 : ZMod 823331149041853)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (2079119063237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (2079119063237, 1)] : List FactorBlock).map factorBlockValue).prod) = 823331149041853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_2079119063237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 823331149041853) ^ 411665574520926 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 823331149041853) ^ 274443716347284 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 823331149041853) ^ 74848286276532 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 823331149041853) ^ 396 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1101824571111907 : Nat.Prime 1101824571111907 := by
  apply lucas_primality 1101824571111907 (2 : ZMod 1101824571111907)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (183637428518651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (183637428518651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101824571111907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_183637428518651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1101824571111907) ^ 550912285555953 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101824571111907) ^ 367274857037302 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101824571111907) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2304725644927109 : Nat.Prime 2304725644927109 := by
  apply lucas_primality 2304725644927109 (2 : ZMod 2304725644927109)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (44321647017829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (44321647017829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2304725644927109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_44321647017829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2304725644927109) ^ 1152362822463554 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304725644927109) ^ 177286588071316 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304725644927109) ^ 52 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2625664727991341 : Nat.Prime 2625664727991341 := by
  apply lucas_primality 2625664727991341 (3 : ZMod 2625664727991341)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41, 1), (457432879441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41, 1), (457432879441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2625664727991341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_457432879441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2625664727991341) ^ 1312832363995670 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2625664727991341) ^ 525132945598268 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2625664727991341) ^ 375094961141620 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2625664727991341) ^ 64040603121740 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2625664727991341) ^ 5740 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2723405555631641 : Nat.Prime 2723405555631641 := by
  apply lucas_primality 2723405555631641 (3 : ZMod 2723405555631641)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (127, 1), (233, 1), (19015481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (127, 1), (233, 1), (19015481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2723405555631641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_127
      · exact prime_thirtyEightAJ_233
      · exact prime_thirtyEightAJ_19015481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2723405555631641) ^ 1361702777815820 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 544681111126328 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 247582323239240 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 21444138233320 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 11688435861080 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 143220440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_4407245885620427 : Nat.Prime 4407245885620427 := by
  apply lucas_primality 4407245885620427 (2 : ZMod 4407245885620427)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (126613, 1), (17404397201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (126613, 1), (17404397201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4407245885620427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_126613
      · exact prime_thirtyEightAJ_17404397201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4407245885620427) ^ 2203622942810213 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407245885620427) ^ 34808794402 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407245885620427) ^ 253226 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_5251329455982683 : Nat.Prime 5251329455982683 := by
  apply lucas_primality 5251329455982683 (2 : ZMod 5251329455982683)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2625664727991341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2625664727991341, 1)] : List FactorBlock).map factorBlockValue).prod) = 5251329455982683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_2625664727991341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5251329455982683) ^ 2625664727991341 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5251329455982683) ^ 2 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_6860865944202667 : Nat.Prime 6860865944202667 := by
  apply lucas_primality 6860865944202667 (2 : ZMod 6860865944202667)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 2), (149, 1), (21191, 1), (91199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 2), (149, 1), (21191, 1), (91199, 1)] : List FactorBlock).map factorBlockValue).prod) = 6860865944202667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_149
      · exact prime_thirtyEightAJ_21191
      · exact prime_thirtyEightAJ_91199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6860865944202667) ^ 3430432972101333 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 2286955314734222 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 623715085836606 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 361098207589614 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 46046080162434 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 323763198726 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 75229618134 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_7568356633535251 : Nat.Prime 7568356633535251 := by
  apply lucas_primality 7568356633535251 (11 : ZMod 7568356633535251)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 3), (7, 2), (19, 1), (23, 1), (52362491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 3), (7, 2), (19, 1), (23, 1), (52362491, 1)] : List FactorBlock).map factorBlockValue).prod) = 7568356633535251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_52362491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7568356633535251) ^ 3784178316767625 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 2522785544511750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 1513671326707050 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 1081193804790750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 398334559659750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 329058984066750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 144537750 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_12321433103383177 : Nat.Prime 12321433103383177 := by
  apply lucas_primality 12321433103383177 (5 : ZMod 12321433103383177)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (71, 1), (709, 1), (829, 1), (286103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (71, 1), (709, 1), (829, 1), (286103, 1)] : List FactorBlock).map factorBlockValue).prod) = 12321433103383177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_71
      · exact prime_thirtyEightAJ_709
      · exact prime_thirtyEightAJ_829
      · exact prime_thirtyEightAJ_286103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12321433103383177) ^ 6160716551691588 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 4107144367794392 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 286544955892632 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 173541311315256 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 17378608044264 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 14863007362344 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 43066423992 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_14960684010162791 : Nat.Prime 14960684010162791 := by
  apply lucas_primality 14960684010162791 (19 : ZMod 14960684010162791)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (36489473195519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (36489473195519, 1)] : List FactorBlock).map factorBlockValue).prod) = 14960684010162791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_36489473195519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 14960684010162791) ^ 7480342005081395 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (19 : ZMod 14960684010162791) ^ 2992136802032558 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (19 : ZMod 14960684010162791) ^ 364894731955190 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (19 : ZMod 14960684010162791) ^ 410 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_20398832627253083 : Nat.Prime 20398832627253083 := by
  apply lucas_primality 20398832627253083 (2 : ZMod 20398832627253083)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57493, 1), (177402750137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57493, 1), (177402750137, 1)] : List FactorBlock).map factorBlockValue).prod) = 20398832627253083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_57493
      · exact prime_thirtyEightAJ_177402750137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20398832627253083) ^ 10199416313626541 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20398832627253083) ^ 354805500274 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20398832627253083) ^ 114986 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_23238390442632649 : Nat.Prime 23238390442632649 := by
  apply lucas_primality 23238390442632649 (13 : ZMod 23238390442632649)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (39343, 1), (1295310031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (39343, 1), (1295310031, 1)] : List FactorBlock).map factorBlockValue).prod) = 23238390442632649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_39343
      · exact prime_thirtyEightAJ_1295310031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 23238390442632649) ^ 11619195221316324 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23238390442632649) ^ 7746130147544216 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23238390442632649) ^ 1223073181191192 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23238390442632649) ^ 590661374136 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23238390442632649) ^ 17940408 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_27766698765404659 : Nat.Prime 27766698765404659 := by
  apply lucas_primality 27766698765404659 (2 : ZMod 27766698765404659)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (101173, 1), (1063750837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (101173, 1), (1063750837, 1)] : List FactorBlock).map factorBlockValue).prod) = 27766698765404659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_101173
      · exact prime_thirtyEightAJ_1063750837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27766698765404659) ^ 13883349382702329 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27766698765404659) ^ 9255566255134886 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27766698765404659) ^ 645737180590806 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27766698765404659) ^ 274447715946 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27766698765404659) ^ 26102634 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_46627893857328739 : Nat.Prime 46627893857328739 := by
  apply lucas_primality 46627893857328739 (2 : ZMod 46627893857328739)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12487, 1), (622352498029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12487, 1), (622352498029, 1)] : List FactorBlock).map factorBlockValue).prod) = 46627893857328739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_12487
      · exact prime_thirtyEightAJ_622352498029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46627893857328739) ^ 23313946928664369 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46627893857328739) ^ 15542631285776246 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46627893857328739) ^ 3734114988174 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46627893857328739) ^ 74922 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_51384630581148941 : Nat.Prime 51384630581148941 := by
  apply lucas_primality 51384630581148941 (7 : ZMod 51384630581148941)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (461, 1), (1083319, 1), (5144533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (461, 1), (1083319, 1), (5144533, 1)] : List FactorBlock).map factorBlockValue).prod) = 51384630581148941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_461
      · exact prime_thirtyEightAJ_1083319
      · exact prime_thirtyEightAJ_5144533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51384630581148941) ^ 25692315290574470 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 51384630581148941) ^ 10276926116229788 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 51384630581148941) ^ 111463406900540 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 51384630581148941) ^ 47432594260 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 51384630581148941) ^ 9988201180 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_64662795067204513 : Nat.Prime 64662795067204513 := by
  apply lucas_primality 64662795067204513 (5 : ZMod 64662795067204513)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (40099, 1), (5599231751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (40099, 1), (5599231751, 1)] : List FactorBlock).map factorBlockValue).prod) = 64662795067204513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_40099
      · exact prime_thirtyEightAJ_5599231751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64662795067204513) ^ 32331397533602256 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 64662795067204513) ^ 21554265022401504 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 64662795067204513) ^ 1612578744288 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 64662795067204513) ^ 11548512 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_73928598620299063 : Nat.Prime 73928598620299063 := by
  apply lucas_primality 73928598620299063 (5 : ZMod 73928598620299063)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12321433103383177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12321433103383177, 1)] : List FactorBlock).map factorBlockValue).prod) = 73928598620299063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_12321433103383177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73928598620299063) ^ 36964299310149531 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73928598620299063) ^ 24642866206766354 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73928598620299063) ^ 6 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_85033748923160677 : Nat.Prime 85033748923160677 := by
  apply lucas_primality 85033748923160677 (2 : ZMod 85033748923160677)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (3327677, 1), (21953167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (3327677, 1), (21953167, 1)] : List FactorBlock).map factorBlockValue).prod) = 85033748923160677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_97
      · exact prime_thirtyEightAJ_3327677
      · exact prime_thirtyEightAJ_21953167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85033748923160677) ^ 42516874461580338 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 85033748923160677) ^ 28344582974386892 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 85033748923160677) ^ 876636586836708 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 85033748923160677) ^ 25553486388 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 85033748923160677) ^ 3873416028 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_86143369831019591 : Nat.Prime 86143369831019591 := by
  apply lucas_primality 86143369831019591 (17 : ZMod 86143369831019591)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (353, 1), (24403220915303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (353, 1), (24403220915303, 1)] : List FactorBlock).map factorBlockValue).prod) = 86143369831019591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_353
      · exact prime_thirtyEightAJ_24403220915303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 86143369831019591) ^ 43071684915509795 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (17 : ZMod 86143369831019591) ^ 17228673966203918 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (17 : ZMod 86143369831019591) ^ 244032209153030 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (17 : ZMod 86143369831019591) ^ 3530 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_88766539549671349 : Nat.Prime 88766539549671349 := by
  apply lucas_primality 88766539549671349 (2 : ZMod 88766539549671349)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (390581, 1), (6312998353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (390581, 1), (6312998353, 1)] : List FactorBlock).map factorBlockValue).prod) = 88766539549671349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_390581
      · exact prime_thirtyEightAJ_6312998353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88766539549671349) ^ 44383269774835674 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 88766539549671349) ^ 29588846516557116 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 88766539549671349) ^ 227267940708 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 88766539549671349) ^ 14060916 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_94736729819765531 : Nat.Prime 94736729819765531 := by
  apply lucas_primality 94736729819765531 (2 : ZMod 94736729819765531)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (193340264938297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (193340264938297, 1)] : List FactorBlock).map factorBlockValue).prod) = 94736729819765531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_193340264938297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94736729819765531) ^ 47368364909882765 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94736729819765531) ^ 18947345963953106 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94736729819765531) ^ 13533818545680790 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94736729819765531) ^ 490 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_121188209303813857 : Nat.Prime 121188209303813857 := by
  apply lucas_primality 121188209303813857 (5 : ZMod 121188209303813857)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (31, 1), (40721844524131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (31, 1), (40721844524131, 1)] : List FactorBlock).map factorBlockValue).prod) = 121188209303813857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_40721844524131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 121188209303813857) ^ 60594104651906928 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 121188209303813857) ^ 40396069767937952 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 121188209303813857) ^ 3909297074316576 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 121188209303813857) ^ 2976 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_130125550443286247 : Nat.Prime 130125550443286247 := by
  apply lucas_primality 130125550443286247 (5 : ZMod 130125550443286247)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (631677429336341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (631677429336341, 1)] : List FactorBlock).map factorBlockValue).prod) = 130125550443286247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_103
      · exact prime_thirtyEightAJ_631677429336341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 130125550443286247) ^ 65062775221643123 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130125550443286247) ^ 1263354858672682 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130125550443286247) ^ 206 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_159026543727295333 : Nat.Prime 159026543727295333 := by
  apply lucas_primality 159026543727295333 (7 : ZMod 159026543727295333)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (389, 1), (3097034815909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (389, 1), (3097034815909, 1)] : List FactorBlock).map factorBlockValue).prod) = 159026543727295333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_389
      · exact prime_thirtyEightAJ_3097034815909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 159026543727295333) ^ 79513271863647666 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 159026543727295333) ^ 53008847909098444 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 159026543727295333) ^ 14456958520663212 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 159026543727295333) ^ 408808595699988 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 159026543727295333) ^ 51348 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_171832565055736069 : Nat.Prime 171832565055736069 := by
  apply lucas_primality 171832565055736069 (2 : ZMod 171832565055736069)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1961107, 1), (663789307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1961107, 1), (663789307, 1)] : List FactorBlock).map factorBlockValue).prod) = 171832565055736069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_1961107
      · exact prime_thirtyEightAJ_663789307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171832565055736069) ^ 85916282527868034 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 57277521685245356 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 15621142277794188 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 87620188524 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 258866124 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_240814399918246243 : Nat.Prime 240814399918246243 := by
  apply lucas_primality 240814399918246243 (3 : ZMod 240814399918246243)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (77929, 1), (2754168409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (77929, 1), (2754168409, 1)] : List FactorBlock).map factorBlockValue).prod) = 240814399918246243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_77929
      · exact prime_thirtyEightAJ_2754168409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 240814399918246243) ^ 120407199959123121 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 80271466639415414 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 21892218174386022 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 14165552936367426 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 3090176954898 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 87436338 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_331941292730282491 : Nat.Prime 331941292730282491 := by
  apply lucas_primality 331941292730282491 (10 : ZMod 331941292730282491)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (650865279863299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (650865279863299, 1)] : List FactorBlock).map factorBlockValue).prod) = 331941292730282491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_650865279863299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 331941292730282491) ^ 165970646365141245 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 331941292730282491) ^ 110647097576760830 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 331941292730282491) ^ 66388258546056498 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 331941292730282491) ^ 19525958395898970 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 331941292730282491) ^ 510 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_466616061331839893 : Nat.Prime 466616061331839893 := by
  apply lucas_primality 466616061331839893 (2 : ZMod 466616061331839893)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (139, 1), (76294320034637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (139, 1), (76294320034637, 1)] : List FactorBlock).map factorBlockValue).prod) = 466616061331839893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_139
      · exact prime_thirtyEightAJ_76294320034637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 466616061331839893) ^ 233308030665919946 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 466616061331839893) ^ 42419641939258172 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 466616061331839893) ^ 3356950081524028 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 466616061331839893) ^ 6116 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_500589777363894013 : Nat.Prime 500589777363894013 := by
  apply lucas_primality 500589777363894013 (2 : ZMod 500589777363894013)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (5501341, 1), (176345227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (5501341, 1), (176345227, 1)] : List FactorBlock).map factorBlockValue).prod) = 500589777363894013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_5501341
      · exact prime_thirtyEightAJ_176345227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 500589777363894013) ^ 250294888681947006 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 500589777363894013) ^ 166863259121298004 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 500589777363894013) ^ 11641622729392884 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 500589777363894013) ^ 90994137132 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 500589777363894013) ^ 2838691956 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_528182958942494357 : Nat.Prime 528182958942494357 := by
  apply lucas_primality 528182958942494357 (2 : ZMod 528182958942494357)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (21481, 1), (6147094629469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (21481, 1), (6147094629469, 1)] : List FactorBlock).map factorBlockValue).prod) = 528182958942494357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_21481
      · exact prime_thirtyEightAJ_6147094629469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 528182958942494357) ^ 264091479471247178 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 528182958942494357) ^ 24588378517876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 528182958942494357) ^ 85924 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_61717
      · exact prime_thirtyEightAJ_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_591256368856072237 : Nat.Prime 591256368856072237 := by
  apply lucas_primality 591256368856072237 (6 : ZMod 591256368856072237)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (163, 1), (185233, 1), (1631881507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (163, 1), (185233, 1), (1631881507, 1)] : List FactorBlock).map factorBlockValue).prod) = 591256368856072237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_163
      · exact prime_thirtyEightAJ_185233
      · exact prime_thirtyEightAJ_1631881507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 591256368856072237) ^ 295628184428036118 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 197085456285357412 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 3627339686233572 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 3191960227692 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 362315748 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_618941509535129819 : Nat.Prime 618941509535129819 := by
  apply lucas_primality 618941509535129819 (2 : ZMod 618941509535129819)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1087, 1), (210499, 1), (79559329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1087, 1), (210499, 1), (79559329, 1)] : List FactorBlock).map factorBlockValue).prod) = 618941509535129819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_1087
      · exact prime_thirtyEightAJ_210499
      · exact prime_thirtyEightAJ_79559329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 618941509535129819) ^ 309470754767564909 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 36408324090301754 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 569403412635814 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 2940353681182 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 7779622042 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_841242296483841983 : Nat.Prime 841242296483841983 := by
  apply lucas_primality 841242296483841983 (5 : ZMod 841242296483841983)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (389, 1), (34880267703949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (389, 1), (34880267703949, 1)] : List FactorBlock).map factorBlockValue).prod) = 841242296483841983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_389
      · exact prime_thirtyEightAJ_34880267703949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 841242296483841983) ^ 420621148241920991 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 841242296483841983) ^ 27136848273672322 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 841242296483841983) ^ 2162576597644838 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 841242296483841983) ^ 24118 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_858232378305983971 : Nat.Prime 858232378305983971 := by
  apply lucas_primality 858232378305983971 (2 : ZMod 858232378305983971)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (61, 1), (907, 1), (57451848793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (61, 1), (907, 1), (57451848793, 1)] : List FactorBlock).map factorBlockValue).prod) = 858232378305983971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_61
      · exact prime_thirtyEightAJ_907
      · exact prime_thirtyEightAJ_57451848793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 858232378305983971) ^ 429116189152991985 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 286077459435327990 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 171646475661196794 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 14069383250917770 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 946231949620710 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 14938290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1111149466697709529 : Nat.Prime 1111149466697709529 := by
  apply lucas_primality 1111149466697709529 (7 : ZMod 1111149466697709529)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (2723405555631641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (2723405555631641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1111149466697709529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_2723405555631641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1111149466697709529) ^ 555574733348854764 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111149466697709529) ^ 370383155565903176 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111149466697709529) ^ 65361733335159384 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111149466697709529) ^ 408 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1952024797181142517 : Nat.Prime 1952024797181142517 := by
  apply lucas_primality 1952024797181142517 (5 : ZMod 1952024797181142517)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23238390442632649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23238390442632649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1952024797181142517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_23238390442632649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1952024797181142517) ^ 976012398590571258 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1952024797181142517) ^ 650674932393714172 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1952024797181142517) ^ 278860685311591788 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1952024797181142517) ^ 84 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2031209080292687611 : Nat.Prime 2031209080292687611 := by
  apply lucas_primality 2031209080292687611 (10 : ZMod 2031209080292687611)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (1013, 1), (502541912603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (1013, 1), (502541912603, 1)] : List FactorBlock).map factorBlockValue).prod) = 2031209080292687611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_1013
      · exact prime_thirtyEightAJ_502541912603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2031209080292687611) ^ 1015604540146343805 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2031209080292687611) ^ 677069693430895870 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2031209080292687611) ^ 406241816058537522 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2031209080292687611) ^ 290172725756098230 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2031209080292687611) ^ 106905741068036190 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2031209080292687611) ^ 2005142231285970 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2031209080292687611) ^ 4041870 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2502372378442714627 : Nat.Prime 2502372378442714627 := by
  apply lucas_primality 2502372378442714627 (12 : ZMod 2502372378442714627)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (5477, 1), (2625789748187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (5477, 1), (2625789748187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2502372378442714627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_5477
      · exact prime_thirtyEightAJ_2625789748187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 2502372378442714627) ^ 1251186189221357313 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (12 : ZMod 2502372378442714627) ^ 834124126147571542 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (12 : ZMod 2502372378442714627) ^ 86288702704921194 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (12 : ZMod 2502372378442714627) ^ 456887416184538 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (12 : ZMod 2502372378442714627) ^ 952998 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2722844489849627963 : Nat.Prime 2722844489849627963 := by
  apply lucas_primality 2722844489849627963 (2 : ZMod 2722844489849627963)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (14960684010162791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (14960684010162791, 1)] : List FactorBlock).map factorBlockValue).prod) = 2722844489849627963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_14960684010162791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2722844489849627963) ^ 1361422244924813981 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2722844489849627963) ^ 388977784264232566 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2722844489849627963) ^ 209449576142279074 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2722844489849627963) ^ 182 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_439
      · exact prime_thirtyEightAJ_853
      · exact prime_thirtyEightAJ_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_8603502523500727663 : Nat.Prime 8603502523500727663 := by
  apply lucas_primality 8603502523500727663 (3 : ZMod 8603502523500727663)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (47, 1), (744118882849051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (47, 1), (744118882849051, 1)] : List FactorBlock).map factorBlockValue).prod) = 8603502523500727663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_744118882849051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8603502523500727663) ^ 4301751261750363831 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8603502523500727663) ^ 2867834174500242554 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8603502523500727663) ^ 209841524963432382 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8603502523500727663) ^ 183053245180866546 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8603502523500727663) ^ 11562 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_10009489513770858509 : Nat.Prime 10009489513770858509 := by
  apply lucas_primality 10009489513770858509 (2 : ZMod 10009489513770858509)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2502372378442714627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2502372378442714627, 1)] : List FactorBlock).map factorBlockValue).prod) = 10009489513770858509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_2502372378442714627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10009489513770858509) ^ 5004744756885429254 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10009489513770858509) ^ 4 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_18838423939996660673 : Nat.Prime 18838423939996660673 := by
  apply lucas_primality 18838423939996660673 (3 : ZMod 18838423939996660673)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (200867, 1), (660817, 1), (2217557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (200867, 1), (660817, 1), (2217557, 1)] : List FactorBlock).map factorBlockValue).prod) = 18838423939996660673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_200867
      · exact prime_thirtyEightAJ_660817
      · exact prime_thirtyEightAJ_2217557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18838423939996660673) ^ 9419211969998330336 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18838423939996660673) ^ 93785559300416 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18838423939996660673) ^ 28507777402816 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18838423939996660673) ^ 8495125013696 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_34414010094002910653 : Nat.Prime 34414010094002910653 := by
  apply lucas_primality 34414010094002910653 (2 : ZMod 34414010094002910653)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8603502523500727663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8603502523500727663, 1)] : List FactorBlock).map factorBlockValue).prod) = 34414010094002910653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_8603502523500727663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34414010094002910653) ^ 17207005047001455326 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34414010094002910653) ^ 4 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_68835218653958870033 : Nat.Prime 68835218653958870033 := by
  apply lucas_primality 68835218653958870033 (3 : ZMod 68835218653958870033)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (349, 1), (577, 1), (777181, 1), (886759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (349, 1), (577, 1), (777181, 1), (886759, 1)] : List FactorBlock).map factorBlockValue).prod) = 68835218653958870033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_349
      · exact prime_thirtyEightAJ_577
      · exact prime_thirtyEightAJ_777181
      · exact prime_thirtyEightAJ_886759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68835218653958870033) ^ 34417609326979435016 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 68835218653958870033) ^ 2220490924321253872 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 68835218653958870033) ^ 197235583535698768 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 68835218653958870033) ^ 119298472537190416 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 68835218653958870033) ^ 88570382773072 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 68835218653958870033) ^ 77625621678448 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_128592066474141292489 : Nat.Prime 128592066474141292489 := by
  apply lucas_primality 128592066474141292489 (7 : ZMod 128592066474141292489)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (307, 1), (487, 1), (3533, 1), (10143596371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (307, 1), (487, 1), (3533, 1), (10143596371, 1)] : List FactorBlock).map factorBlockValue).prod) = 128592066474141292489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_307
      · exact prime_thirtyEightAJ_487
      · exact prime_thirtyEightAJ_3533
      · exact prime_thirtyEightAJ_10143596371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 128592066474141292489) ^ 64296033237070646244 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 42864022158047097496 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 418866666039548184 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 264049417811378424 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 36397414795964136 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 12677167128 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_171369045757508972531 : Nat.Prime 171369045757508972531 := by
  apply lucas_primality 171369045757508972531 (2 : ZMod 171369045757508972531)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (2621, 1), (344121459783347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (2621, 1), (344121459783347, 1)] : List FactorBlock).map factorBlockValue).prod) = 171369045757508972531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_2621
      · exact prime_thirtyEightAJ_344121459783347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171369045757508972531) ^ 85684522878754486265 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 34273809151501794506 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 9019423460921524870 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 65383077358835930 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 497990 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_183386141468582607671 : Nat.Prime 183386141468582607671 := by
  apply lucas_primality 183386141468582607671 (7 : ZMod 183386141468582607671)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (277, 1), (33359, 1), (25121561411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (277, 1), (33359, 1), (25121561411, 1)] : List FactorBlock).map factorBlockValue).prod) = 183386141468582607671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_79
      · exact prime_thirtyEightAJ_277
      · exact prime_thirtyEightAJ_33359
      · exact prime_thirtyEightAJ_25121561411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 183386141468582607671) ^ 91693070734291303835 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 36677228293716521534 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 2321343562893450730 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 662043832016543710 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 5497351283569130 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 7299949970 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_186858651670165057673 : Nat.Prime 186858651670165057673 := by
  apply lucas_primality 186858651670165057673 (3 : ZMod 186858651670165057673)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (653, 1), (2843, 1), (177204535801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (653, 1), (2843, 1), (177204535801, 1)] : List FactorBlock).map factorBlockValue).prod) = 186858651670165057673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_71
      · exact prime_thirtyEightAJ_653
      · exact prime_thirtyEightAJ_2843
      · exact prime_thirtyEightAJ_177204535801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 186858651670165057673) ^ 93429325835082528836 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 2631811995354437432 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 286154137320314024 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 65725871146734104 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 1054480072 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_233705488596142099613 : Nat.Prime 233705488596142099613 := by
  apply lucas_primality 233705488596142099613 (2 : ZMod 233705488596142099613)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (449, 1), (130125550443286247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (449, 1), (130125550443286247, 1)] : List FactorBlock).map factorBlockValue).prod) = 233705488596142099613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_449
      · exact prime_thirtyEightAJ_130125550443286247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 233705488596142099613) ^ 116852744298071049806 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233705488596142099613) ^ 520502201773144988 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233705488596142099613) ^ 1796 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_235552676694175913491 : Nat.Prime 235552676694175913491 := by
  apply lucas_primality 235552676694175913491 (11 : ZMod 235552676694175913491)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (167, 1), (5927, 1), (71707, 1), (3352277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (167, 1), (5927, 1), (71707, 1), (3352277, 1)] : List FactorBlock).map factorBlockValue).prod) = 235552676694175913491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_167
      · exact prime_thirtyEightAJ_5927
      · exact prime_thirtyEightAJ_71707
      · exact prime_thirtyEightAJ_3352277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 235552676694175913491) ^ 117776338347087956745 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 78517558898058637830 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 47110535338835182698 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 21413879699470537590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 1410495070025005470 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 39742310898291870 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 3284932805642070 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (11 : ZMod 235552676694175913491) ^ 70266471623370 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_699089860196274954313 : Nat.Prime 699089860196274954313 := by
  apply lucas_primality 699089860196274954313 (15 : ZMod 699089860196274954313)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (41669, 1), (13706876732477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (41669, 1), (13706876732477, 1)] : List FactorBlock).map factorBlockValue).prod) = 699089860196274954313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_41669
      · exact prime_thirtyEightAJ_13706876732477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 699089860196274954313) ^ 349544930098137477156 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 699089860196274954313) ^ 233029953398758318104 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 699089860196274954313) ^ 41122932952722056136 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 699089860196274954313) ^ 16777217120551848 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (15 : ZMod 699089860196274954313) ^ 51002856 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_702440291331326015581 : Nat.Prime 702440291331326015581 := by
  apply lucas_primality 702440291331326015581 (10 : ZMod 702440291331326015581)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (199, 1), (6967, 1), (41593, 1), (1000099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (199, 1), (6967, 1), (41593, 1), (1000099, 1)] : List FactorBlock).map factorBlockValue).prod) = 702440291331326015581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_199
      · exact prime_thirtyEightAJ_6967
      · exact prime_thirtyEightAJ_41593
      · exact prime_thirtyEightAJ_1000099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 702440291331326015581) ^ 351220145665663007790 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 234146763777108671860 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 140488058266265203116 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 100348613047332287940 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 24222079011425035020 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 3529850710207668420 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 100823925840580740 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 16888425728640060 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 702440291331326015581) ^ 702370756626420 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_742167410374799740327 : Nat.Prime 742167410374799740327 := by
  apply lucas_primality 742167410374799740327 (5 : ZMod 742167410374799740327)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (857, 1), (76471, 1), (1887439493743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (857, 1), (76471, 1), (1887439493743, 1)] : List FactorBlock).map factorBlockValue).prod) = 742167410374799740327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_857
      · exact prime_thirtyEightAJ_76471
      · exact prime_thirtyEightAJ_1887439493743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 742167410374799740327) ^ 371083705187399870163 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 742167410374799740327) ^ 247389136791599913442 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 742167410374799740327) ^ 866006313156125718 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 742167410374799740327) ^ 9705213876826506 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 742167410374799740327) ^ 393213882 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_897784781005376023787 : Nat.Prime 897784781005376023787 := by
  apply lucas_primality 897784781005376023787 (2 : ZMod 897784781005376023787)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (389, 1), (88766539549671349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (389, 1), (88766539549671349, 1)] : List FactorBlock).map factorBlockValue).prod) = 897784781005376023787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_389
      · exact prime_thirtyEightAJ_88766539549671349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 897784781005376023787) ^ 448892390502688011893 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 897784781005376023787) ^ 69060367769644309522 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 897784781005376023787) ^ 2307930028291455074 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 897784781005376023787) ^ 10114 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1198819905425913042347 : Nat.Prime 1198819905425913042347 := by
  apply lucas_primality 1198819905425913042347 (2 : ZMod 1198819905425913042347)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20426557391, 1), (29344639003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20426557391, 1), (29344639003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198819905425913042347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_20426557391
      · exact prime_thirtyEightAJ_29344639003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1198819905425913042347) ^ 599409952712956521173 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198819905425913042347) ^ 58689278006 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198819905425913042347) ^ 40853114782 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2103430313680430835511 : Nat.Prime 2103430313680430835511 := by
  apply lucas_primality 2103430313680430835511 (6 : ZMod 2103430313680430835511)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (89, 1), (251, 1), (4079, 1), (256488670019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (89, 1), (251, 1), (4079, 1), (256488670019, 1)] : List FactorBlock).map factorBlockValue).prod) = 2103430313680430835511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_89
      · exact prime_thirtyEightAJ_251
      · exact prime_thirtyEightAJ_4079
      · exact prime_thirtyEightAJ_256488670019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2103430313680430835511) ^ 1051715156840215417755 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2103430313680430835511) ^ 701143437893476945170 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2103430313680430835511) ^ 420686062736086167102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2103430313680430835511) ^ 23634048468319447590 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2103430313680430835511) ^ 8380200452910083010 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2103430313680430835511) ^ 515673035959899690 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2103430313680430835511) ^ 8200870290 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_107
      · exact prime_thirtyEightAJ_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_8343050382369831510029 : Nat.Prime 8343050382369831510029 := by
  apply lucas_primality 8343050382369831510029 (2 : ZMod 8343050382369831510029)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2153, 1), (53225903, 1), (18201107173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2153, 1), (53225903, 1), (18201107173, 1)] : List FactorBlock).map factorBlockValue).prod) = 8343050382369831510029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_2153
      · exact prime_thirtyEightAJ_53225903
      · exact prime_thirtyEightAJ_18201107173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8343050382369831510029) ^ 4171525191184915755014 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8343050382369831510029) ^ 3875081459530808876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8343050382369831510029) ^ 156747934973876 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8343050382369831510029) ^ 458381476636 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_12074758012653445959791 : Nat.Prime 12074758012653445959791 := by
  apply lucas_primality 12074758012653445959791 (14 : ZMod 12074758012653445959791)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (16333, 1), (73928598620299063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (16333, 1), (73928598620299063, 1)] : List FactorBlock).map factorBlockValue).prod) = 12074758012653445959791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_16333
      · exact prime_thirtyEightAJ_73928598620299063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 12074758012653445959791) ^ 6037379006326722979895 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 12074758012653445959791) ^ 2414951602530689191958 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 12074758012653445959791) ^ 739285986202990630 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (14 : ZMod 12074758012653445959791) ^ 163330 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_12452068472553829032367 : Nat.Prime 12452068472553829032367 := by
  apply lucas_primality 12452068472553829032367 (3 : ZMod 12452068472553829032367)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2467, 1), (841242296483841983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2467, 1), (841242296483841983, 1)] : List FactorBlock).map factorBlockValue).prod) = 12452068472553829032367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_2467
      · exact prime_thirtyEightAJ_841242296483841983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12452068472553829032367) ^ 6226034236276914516183 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452068472553829032367) ^ 4150689490851276344122 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452068472553829032367) ^ 5047453778903051898 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452068472553829032367) ^ 14802 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_14240133936556782272833 : Nat.Prime 14240133936556782272833 := by
  apply lucas_primality 14240133936556782272833 (7 : ZMod 14240133936556782272833)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (89, 1), (97, 1), (733, 1), (1065502430449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (89, 1), (97, 1), (733, 1), (1065502430449, 1)] : List FactorBlock).map factorBlockValue).prod) = 14240133936556782272833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_89
      · exact prime_thirtyEightAJ_97
      · exact prime_thirtyEightAJ_733
      · exact prime_thirtyEightAJ_1065502430449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14240133936556782272833) ^ 7120066968278391136416 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 4746711312185594090944 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 1294557630596071115712 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 160001504905132385088 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 146805504500585384256 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 19427195002123850304 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 13364712768 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_25510461207144931604987 : Nat.Prime 25510461207144931604987 := by
  apply lucas_primality 25510461207144931604987 (2 : ZMod 25510461207144931604987)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (251, 1), (2843, 1), (246833, 1), (10345142371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (251, 1), (2843, 1), (246833, 1), (10345142371, 1)] : List FactorBlock).map factorBlockValue).prod) = 25510461207144931604987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_251
      · exact prime_thirtyEightAJ_2843
      · exact prime_thirtyEightAJ_246833
      · exact prime_thirtyEightAJ_10345142371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25510461207144931604987) ^ 12755230603572465802493 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25510461207144931604987) ^ 3644351601020704514998 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25510461207144931604987) ^ 101635303614123233486 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25510461207144931604987) ^ 8973078159389705102 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25510461207144931604987) ^ 103351096519286042 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25510461207144931604987) ^ 2465936213566 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_39703327656062808021443 : Nat.Prime 39703327656062808021443 := by
  apply lucas_primality 39703327656062808021443 (2 : ZMod 39703327656062808021443)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1709, 1), (359419759, 1), (32318626891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1709, 1), (359419759, 1), (32318626891, 1)] : List FactorBlock).map factorBlockValue).prod) = 39703327656062808021443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_1709
      · exact prime_thirtyEightAJ_359419759
      · exact prime_thirtyEightAJ_32318626891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39703327656062808021443) ^ 19851663828031404010721 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39703327656062808021443) ^ 23231906176748278538 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39703327656062808021443) ^ 110465066713438 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39703327656062808021443) ^ 1228496736262 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_309540861772294272798521 : Nat.Prime 309540861772294272798521 := by
  apply lucas_primality 309540861772294272798521 (3 : ZMod 309540861772294272798521)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 1), (10253, 1), (20398832627253083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 1), (10253, 1), (20398832627253083, 1)] : List FactorBlock).map factorBlockValue).prod) = 309540861772294272798521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_10253
      · exact prime_thirtyEightAJ_20398832627253083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 309540861772294272798521) ^ 154770430886147136399260 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 61908172354458854559704 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 8365969237089034399960 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 30190272288334562840 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 15174440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_478370245391122250603543 : Nat.Prime 478370245391122250603543 := by
  apply lucas_primality 478370245391122250603543 (5 : ZMod 478370245391122250603543)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (641, 1), (10151, 1), (5251329455982683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (641, 1), (10151, 1), (5251329455982683, 1)] : List FactorBlock).map factorBlockValue).prod) = 478370245391122250603543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_641
      · exact prime_thirtyEightAJ_10151
      · exact prime_thirtyEightAJ_5251329455982683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 478370245391122250603543) ^ 239185122695561125301771 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 478370245391122250603543) ^ 68338606484446035800506 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 478370245391122250603543) ^ 746287434307523011862 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 478370245391122250603543) ^ 47125430537988597242 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 478370245391122250603543) ^ 91095074 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_591226793650408566687263 : Nat.Prime 591226793650408566687263 := by
  apply lucas_primality 591226793650408566687263 (5 : ZMod 591226793650408566687263)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43086893, 1), (6860865944202667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43086893, 1), (6860865944202667, 1)] : List FactorBlock).map factorBlockValue).prod) = 591226793650408566687263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_43086893
      · exact prime_thirtyEightAJ_6860865944202667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 591226793650408566687263) ^ 295613396825204283343631 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 591226793650408566687263) ^ 13721731888405334 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 591226793650408566687263) ^ 86173786 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_776060487060066439202483 : Nat.Prime 776060487060066439202483 := by
  apply lucas_primality 776060487060066439202483 (2 : ZMod 776060487060066439202483)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (461, 1), (593, 1), (36497, 1), (94167868097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (461, 1), (593, 1), (36497, 1), (94167868097, 1)] : List FactorBlock).map factorBlockValue).prod) = 776060487060066439202483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_461
      · exact prime_thirtyEightAJ_593
      · exact prime_thirtyEightAJ_36497
      · exact prime_thirtyEightAJ_94167868097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 776060487060066439202483) ^ 388030243530033219601241 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 110865783865723777028926 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 13153567577289261681398 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 1683428388416630019962 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 1308702339055761280274 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 21263678851962255506 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 8241245158706 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_854287809159847994170487 : Nat.Prime 854287809159847994170487 := by
  apply lucas_primality 854287809159847994170487 (5 : ZMod 854287809159847994170487)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (699089860196274954313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (699089860196274954313, 1)] : List FactorBlock).map factorBlockValue).prod) = 854287809159847994170487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_699089860196274954313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 854287809159847994170487) ^ 427143904579923997085243 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 854287809159847994170487) ^ 65714446858449845705422 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 854287809159847994170487) ^ 18176336365103148812138 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 854287809159847994170487) ^ 1222 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1249684049955695303628143 : Nat.Prime 1249684049955695303628143 := by
  apply lucas_primality 1249684049955695303628143 (5 : ZMod 1249684049955695303628143)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1183003, 1), (528182958942494357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1183003, 1), (528182958942494357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249684049955695303628143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_1183003
      · exact prime_thirtyEightAJ_528182958942494357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1249684049955695303628143) ^ 624842024977847651814071 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249684049955695303628143) ^ 1056365917884988714 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249684049955695303628143) ^ 2366006 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1393274665712738290135889 : Nat.Prime 1393274665712738290135889 := by
  apply lucas_primality 1393274665712738290135889 (3 : ZMod 1393274665712738290135889)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (31, 1), (1783, 1), (121188209303813857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (31, 1), (1783, 1), (121188209303813857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393274665712738290135889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_1783
      · exact prime_thirtyEightAJ_121188209303813857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1393274665712738290135889) ^ 696637332856369145067944 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1393274665712738290135889) ^ 107174974285595253087376 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1393274665712738290135889) ^ 44944344055249622262448 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1393274665712738290135889) ^ 781421573590991749936 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1393274665712738290135889) ^ 11496784 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2120257756189874282195089 : Nat.Prime 2120257756189874282195089 := by
  apply lucas_primality 2120257756189874282195089 (13 : ZMod 2120257756189874282195089)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (2103430313680430835511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (2103430313680430835511, 1)] : List FactorBlock).map factorBlockValue).prod) = 2120257756189874282195089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_2103430313680430835511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2120257756189874282195089) ^ 1060128878094937141097544 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 2120257756189874282195089) ^ 706752585396624760731696 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 2120257756189874282195089) ^ 302893965169982040313584 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (13 : ZMod 2120257756189874282195089) ^ 1008 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2787154388976192453963133 : Nat.Prime 2787154388976192453963133 := by
  apply lucas_primality 2787154388976192453963133 (2 : ZMod 2787154388976192453963133)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (199557398321, 1), (1163890027141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (199557398321, 1), (1163890027141, 1)] : List FactorBlock).map factorBlockValue).prod) = 2787154388976192453963133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_199557398321
      · exact prime_thirtyEightAJ_1163890027141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2787154388976192453963133) ^ 1393577194488096226981566 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2787154388976192453963133) ^ 929051462992064151321044 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2787154388976192453963133) ^ 13966680325692 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2787154388976192453963133) ^ 2394688779852 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3006299624993793239121503 : Nat.Prime 3006299624993793239121503 := by
  apply lucas_primality 3006299624993793239121503 (5 : ZMod 3006299624993793239121503)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52600248139, 1), (28576857822509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52600248139, 1), (28576857822509, 1)] : List FactorBlock).map factorBlockValue).prod) = 3006299624993793239121503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_52600248139
      · exact prime_thirtyEightAJ_28576857822509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3006299624993793239121503) ^ 1503149812496896619560751 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3006299624993793239121503) ^ 57153715645018 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3006299624993793239121503) ^ 105200496278 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3246108496814107381895357 : Nat.Prime 3246108496814107381895357 := by
  apply lucas_primality 3246108496814107381895357 (2 : ZMod 3246108496814107381895357)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (101, 1), (186858651670165057673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (101, 1), (186858651670165057673, 1)] : List FactorBlock).map factorBlockValue).prod) = 3246108496814107381895357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_101
      · exact prime_thirtyEightAJ_186858651670165057673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3246108496814107381895357) ^ 1623054248407053690947678 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246108496814107381895357) ^ 75490895274746683299892 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246108496814107381895357) ^ 32139688087268389919756 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246108496814107381895357) ^ 17372 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3690032163934886748700759 : Nat.Prime 3690032163934886748700759 := by
  apply lucas_primality 3690032163934886748700759 (6 : ZMod 3690032163934886748700759)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (397, 1), (6199, 1), (27766698765404659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (397, 1), (6199, 1), (27766698765404659, 1)] : List FactorBlock).map factorBlockValue).prod) = 3690032163934886748700759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_397
      · exact prime_thirtyEightAJ_6199
      · exact prime_thirtyEightAJ_27766698765404659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3690032163934886748700759) ^ 1845016081967443374350379 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3690032163934886748700759) ^ 1230010721311628916233586 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3690032163934886748700759) ^ 9294791344924147981614 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3690032163934886748700759) ^ 595262488132745079642 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3690032163934886748700759) ^ 132894162 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_10727349951267250755833749 : Nat.Prime 10727349951267250755833749 := by
  apply lucas_primality 10727349951267250755833749 (2 : ZMod 10727349951267250755833749)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (13009, 1), (253697251, 1), (9340143089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (13009, 1), (253697251, 1), (9340143089, 1)] : List FactorBlock).map factorBlockValue).prod) = 10727349951267250755833749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_13009
      · exact prime_thirtyEightAJ_253697251
      · exact prime_thirtyEightAJ_9340143089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10727349951267250755833749) ^ 5363674975633625377916874 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 3575783317089083585277916 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 369908619009215543304612 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 824609881717830021972 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 42284060662790748 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 1148520943314132 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_18122687210934750369274603 : Nat.Prime 18122687210934750369274603 := by
  apply lucas_primality 18122687210934750369274603 (2 : ZMod 18122687210934750369274603)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (67, 1), (2927, 1), (2976671, 1), (470381570423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (67, 1), (2927, 1), (2976671, 1), (470381570423, 1)] : List FactorBlock).map factorBlockValue).prod) = 18122687210934750369274603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_2927
      · exact prime_thirtyEightAJ_2976671
      · exact prime_thirtyEightAJ_470381570423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18122687210934750369274603) ^ 9061343605467375184637301 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18122687210934750369274603) ^ 6040895736978250123091534 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18122687210934750369274603) ^ 1647517019175886397206782 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18122687210934750369274603) ^ 270487868819921647302606 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18122687210934750369274603) ^ 6191556956246925305526 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18122687210934750369274603) ^ 6088239920009551062 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18122687210934750369274603) ^ 38527630227174 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_49207164946229185285248347 : Nat.Prime 49207164946229185285248347 := by
  apply lucas_primality 49207164946229185285248347 (5 : ZMod 49207164946229185285248347)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (467, 1), (7499, 1), (29531, 1), (5802512756111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (467, 1), (7499, 1), (29531, 1), (5802512756111, 1)] : List FactorBlock).map factorBlockValue).prod) = 49207164946229185285248347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_467
      · exact prime_thirtyEightAJ_7499
      · exact prime_thirtyEightAJ_29531
      · exact prime_thirtyEightAJ_5802512756111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49207164946229185285248347) ^ 24603582473114592642624173 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49207164946229185285248347) ^ 1200174754786077689884106 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49207164946229185285248347) ^ 105368661555094615171838 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49207164946229185285248347) ^ 6561830236862139656654 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49207164946229185285248347) ^ 1666288474695377240366 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49207164946229185285248347) ^ 8480319994886 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_103041609164924876526219589 : Nat.Prime 103041609164924876526219589 := by
  apply lucas_primality 103041609164924876526219589 (2 : ZMod 103041609164924876526219589)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (67, 1), (14240133936556782272833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (67, 1), (14240133936556782272833, 1)] : List FactorBlock).map factorBlockValue).prod) = 103041609164924876526219589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_67
      · exact prime_thirtyEightAJ_14240133936556782272833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103041609164924876526219589) ^ 51520804582462438263109794 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103041609164924876526219589) ^ 34347203054974958842073196 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103041609164924876526219589) ^ 1537934465148132485465964 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103041609164924876526219589) ^ 7236 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_493693863691288419400348801 : Nat.Prime 493693863691288419400348801 := by
  apply lucas_primality 493693863691288419400348801 (26 : ZMod 493693863691288419400348801)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 493693863691288419400348801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 493693863691288419400348801) ^ 246846931845644209700174400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 164564621230429473133449600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 98738772738257683880069760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 70527694813041202771478400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 44881260335571674490940800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 29040815511252259964726400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 25983887562699390494755200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 21464950595273409539145600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 17023926334182359289667200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 15925608506170594174204800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 13343077397061849172982400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 12041313748568010229276800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 11481252643983451613961600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 10504124759389115306390400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 9314978560212989045289600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 8367692604937091854243200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (26 : ZMod 493693863691288419400348801) ^ 8093342027726039662300800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_528542842304791131358020481 : Nat.Prime 528542842304791131358020481 := by
  apply lucas_primality 528542842304791131358020481 (89 : ZMod 528542842304791131358020481)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 528542842304791131358020481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 528542842304791131358020481) ^ 264271421152395565679010240 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 176180947434930377119340160 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 105708568460958226271604096 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 75506120329255875908288640 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 48049349300435557396183680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 40657141715753163950616960 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 27818044331831112176737920 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 22980123578469179624261760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 18225615251889349357173120 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 17049769106606165527678080 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 14284941683913273820487040 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 12891288836702222716049280 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 12291694007088165845535360 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 11245592389463641092723840 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 9972506458580964742604160 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 8958353259403239514542720 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (89 : ZMod 528542842304791131358020481) ^ 8664636759094936579639680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_680699115089503729779268801 : Nat.Prime 680699115089503729779268801 := by
  apply lucas_primality 680699115089503729779268801 (67 : ZMod 680699115089503729779268801)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 680699115089503729779268801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 680699115089503729779268801) ^ 340349557544751864889634400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 226899705029834576593089600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 136139823017900745955853760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 97242730727071961397038400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 52361470391500286906097600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 40041124417029631163486400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 35826269215237038409435200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 29595613699543640425185600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 23472383278948404475147200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 21958035970629152573524800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 18397273380797398102142400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 16602417441207408043396800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 15830211978825668134401600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 14482959895521355952750400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 12843379529990636410929600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 11537273137110232708123200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 11159001886713175898020800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_724615187030762034926318401 : Nat.Prime 724615187030762034926318401 := by
  apply lucas_primality 724615187030762034926318401 (62 : ZMod 724615187030762034926318401)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 724615187030762034926318401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (62 : ZMod 724615187030762034926318401) ^ 362307593515381017463159200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 241538395676920678308772800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 144923037406152406985263680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 103516455290108862132331200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 65874107911887457720574400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 55739629771597079609716800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 42624422766515413819195200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 38137641422671686048753600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 31505008131772262388100800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 24986730587267656376769600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 19584194244074649592603200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 17673541147091756949422400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 16851515977459582207588800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 15417344404909830530347200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 13671984660957774243892800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 12281613339504441269937600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 11878937492307574343054400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_916860032569535636029219201 : Nat.Prime 916860032569535636029219201 := by
  apply lucas_primality 916860032569535636029219201 (28 : ZMod 916860032569535636029219201)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 916860032569535636029219201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 916860032569535636029219201) ^ 458430016284767818014609600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 305620010856511878676406400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 183372006513907127205843840 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 83350912051775966911747200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 70527694813041202771478400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 53932943092325625648777600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 48255791187870296633116800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 39863479676936332001270400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 31615863192052952966524800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 29576130082888246323523200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 24780000880257719892681600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 22362439818769161854371200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 21322326338826410140214400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 19507660267436928426153600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 17299245897538408226966400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 15540000552026027729308800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (28 : ZMod 916860032569535636029219201) ^ 15030492337205502229987200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1321357105761977828395051201 : Nat.Prime 1321357105761977828395051201 := by
  apply lucas_primality 1321357105761977828395051201 (83 : ZMod 1321357105761977828395051201)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1321357105761977828395051201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1321357105761977828395051201) ^ 660678552880988914197525600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 440452368587325942798350400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 264271421152395565679010240 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 188765300823139689770721600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 120123373251088893490459200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 101642854289382909876542400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 69545110829577780441844800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 57450308946172949060654400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 45564038129723373392932800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 42624422766515413819195200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 35712354209783184551217600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 32228222091755556790123200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 30729235017720414613838400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 28113980973659102731809600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 24931266146452411856510400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 22395883148508098786356800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 21661591897737341449099200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1497538053196908205514391361 : Nat.Prime 1497538053196908205514391361 := by
  apply lucas_primality 1497538053196908205514391361 (134 : ZMod 1497538053196908205514391361)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497538053196908205514391361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (134 : ZMod 1497538053196908205514391361) ^ 748769026598454102757195680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 499179351065636068504797120 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 299507610639381641102878272 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 213934007599558315073484480 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 136139823017900745955853760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 115195234861300631193414720 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 88090473717465188559670080 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 65110350138996008935408320 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 51639243213686489845323840 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 48307679135384135661754560 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 40474001437754275824713280 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 36525318370656297695472960 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 34826466353416469895683520 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 31862511770146983096050880 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 28255434965979400104045120 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 25382000901642511957871040 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 24549804150768986975645760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_1871922566496135256892989201 : Nat.Prime 1871922566496135256892989201 := by
  apply lucas_primality 1871922566496135256892989201 (101 : ZMod 1871922566496135256892989201)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1871922566496135256892989201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1871922566496135256892989201) ^ 935961283248067628446494600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 623974188832045085630996400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 374384513299227051378597840 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 267417509499447893841855600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 170174778772375932444817200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 143994043576625788991768400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 110113092146831485699587600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 98522240341901855625946800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 81387937673745011169260400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 64549054017108112306654800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 60384598919230169577193200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 50592501797192844780891600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 45656647963320372119341200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 43533082941770587369604400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 39828139712683728870063600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 35319293707474250130056400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 31727501127053139947338800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 30687255188461233719557200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2246307079795362308271587041 : Nat.Prime 2246307079795362308271587041 := by
  apply lucas_primality 2246307079795362308271587041 (73 : ZMod 2246307079795362308271587041)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2246307079795362308271587041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 2246307079795362308271587041) ^ 1123153539897681154135793520 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 748769026598454102757195680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 449261415959072461654317408 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 320901011399337472610226720 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 204209734526851118933780640 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 172792852291950946790122080 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 132135710576197782839505120 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 118226688410282226751136160 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 97665525208494013403112480 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 77458864820529734767985760 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 72461518703076203492631840 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 60711002156631413737069920 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 54787977555984446543209440 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 52239699530124704843525280 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 47793767655220474644076320 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 42383152448969100156067680 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 38073001352463767936806560 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 36824706226153480463468640 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_2642714211523955656790102401 : Nat.Prime 2642714211523955656790102401 := by
  apply lucas_primality 2642714211523955656790102401 (34 : ZMod 2642714211523955656790102401)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2642714211523955656790102401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 2642714211523955656790102401) ^ 1321357105761977828395051200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 880904737174651885596700800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 528542842304791131358020480 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 377530601646279379541443200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 240246746502177786980918400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 203285708578765819753084800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 139090221659155560883689600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 114900617892345898121308800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 91128076259446746785865600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 85248845533030827638390400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 71424708419566369102435200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 64456444183511113580246400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 61458470035440829227676800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 56227961947318205463619200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 49862532292904823713020800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 44791766297016197572713600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (34 : ZMod 2642714211523955656790102401) ^ 43323183795474682898198400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_3455857045839018935802441601 : Nat.Prime 3455857045839018935802441601 := by
  apply lucas_primality 3455857045839018935802441601 (109 : ZMod 3455857045839018935802441601)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3455857045839018935802441601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (109 : ZMod 3455857045839018935802441601) ^ 1727928522919509467901220800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 1151952348613006311934147200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 691171409167803787160488320 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 493693863691288419400348800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 314168822349001721436585600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 203285708578765819753084800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 181887212938895733463286400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 150254654166913866774019200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 119167484339276515027670400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 111479259543194159219433600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 93401541779432944210876800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 84289196239976071604937600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 80368768507884161297731200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 73528873315723807144732800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 65204849921490923317027200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 58573848234559642979702400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (109 : ZMod 3455857045839018935802441601) ^ 56653394194082277636105600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_14975380531969082055143913601 : Nat.Prime 14975380531969082055143913601 := by
  apply lucas_primality 14975380531969082055143913601 (67 : ZMod 14975380531969082055143913601)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 14975380531969082055143913601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_5
      · exact prime_thirtyEightAJ_7
      · exact prime_thirtyEightAJ_11
      · exact prime_thirtyEightAJ_13
      · exact prime_thirtyEightAJ_17
      · exact prime_thirtyEightAJ_19
      · exact prime_thirtyEightAJ_23
      · exact prime_thirtyEightAJ_29
      · exact prime_thirtyEightAJ_31
      · exact prime_thirtyEightAJ_37
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_43
      · exact prime_thirtyEightAJ_47
      · exact prime_thirtyEightAJ_53
      · exact prime_thirtyEightAJ_59
      · exact prime_thirtyEightAJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 14975380531969082055143913601) ^ 7487690265984541027571956800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 4991793510656360685047971200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 2995076106393816411028782720 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 2139340075995583150734844800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 1361398230179007459558537600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 1151952348613006311934147200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 880904737174651885596700800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 788177922735214845007574400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 651103501389960089354083200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 516392432136864898453238400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 483076791353841356617545600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 404740014377542758247132800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 365253183706562976954729600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 348264663534164698956835200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 318625117701469830960508800 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 282554349659794001040451200 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 253820009016425119578710400 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (67 : ZMod 14975380531969082055143913601) ^ 245498041507689869756457600 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_44926141595907246165431740873 : Nat.Prime 44926141595907246165431740873 := by
  apply lucas_primality 44926141595907246165431740873 (5 : ZMod 44926141595907246165431740873)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1337232557, 1), (466616061331839893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1337232557, 1), (466616061331839893, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_3
      · exact prime_thirtyEightAJ_1337232557
      · exact prime_thirtyEightAJ_466616061331839893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44926141595907246165431740873) ^ 22463070797953623082715870436 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44926141595907246165431740873) ^ 14975380531969082055143913624 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44926141595907246165431740873) ^ 33596356415892472296 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44926141595907246165431740873) ^ 96280744104 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem prime_thirtyEightAJ_44926141595907246165431740883 : Nat.Prime 44926141595907246165431740883 := by
  apply lucas_primality 44926141595907246165431740883 (2 : ZMod 44926141595907246165431740883)
  · rw [← thirtyEightAJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (97, 1), (677, 1), (8343050382369831510029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (97, 1), (677, 1), (8343050382369831510029, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyEightAJ_2
      · exact prime_thirtyEightAJ_41
      · exact prime_thirtyEightAJ_97
      · exact prime_thirtyEightAJ_677
      · exact prime_thirtyEightAJ_8343050382369831510029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44926141595907246165431740883) ^ 22463070797953623082715870441 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907246165431740883) ^ 1095759551119688930864188802 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907246165431740883) ^ 463156098926878826447749906 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907246165431740883) ^ 66360622741369639830770666 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907246165431740883) ^ 5384858 ≠ 1
      rw [← thirtyEightAJFastPow_eq_pow]
      decide

private theorem phi_thirtyEightAJ_44926141595907246165431740800 : Nat.totient 44926141595907246165431740800 = 5911712001455704296652800000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_7, prime_thirtyEightAJ_11, prime_thirtyEightAJ_13, prime_thirtyEightAJ_17, prime_thirtyEightAJ_19, prime_thirtyEightAJ_23, prime_thirtyEightAJ_29, prime_thirtyEightAJ_31, prime_thirtyEightAJ_37, prime_thirtyEightAJ_41, prime_thirtyEightAJ_43, prime_thirtyEightAJ_47, prime_thirtyEightAJ_53, prime_thirtyEightAJ_59, prime_thirtyEightAJ_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740801 : Nat.totient 44926141595907246165431740801 = 44908391243612418375906690000 := by
  rw [← show ((([(2531, 1), (2432604289021, 1), (7296851506151, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2531, prime_thirtyEightAJ_2432604289021, prime_thirtyEightAJ_7296851506151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740802 : Nat.totient 44926141595907246165431740802 = 22448371843838548766018027520 := by
  rw [← show ((([(2, 1), (1657, 1), (23041, 1), (133499, 1), (4407245885620427, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_1657, prime_thirtyEightAJ_23041, prime_thirtyEightAJ_133499, prime_thirtyEightAJ_4407245885620427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740803 : Nat.totient 44926141595907246165431740803 = 29950761063938164110287827200 := by
  rw [← show ((([(3, 1), (14975380531969082055143913601, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_14975380531969082055143913601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740804 : Nat.totient 44926141595907246165431740804 = 22256987579623773329663431008 := by
  rw [← show ((([(2, 2), (109, 1), (103041609164924876526219589, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_109, prime_thirtyEightAJ_103041609164924876526219589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740805 : Nat.totient 44926141595907246165431740805 = 35935340178062945979184823296 := by
  rw [← show ((([(5, 1), (6449, 1), (1393274665712738290135889, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_6449, prime_thirtyEightAJ_1393274665712738290135889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740806 : Nat.totient 44926141595907246165431740806 = 14975356382453056748250753800 := by
  rw [← show ((([(2, 1), (3, 1), (620111, 1), (12074758012653445959791, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_620111, prime_thirtyEightAJ_12074758012653445959791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740807 : Nat.totient 44926141595907246165431740807 = 38502550668423529259733627648 := by
  rw [← show ((([(7, 1), (6917, 1), (10911689, 1), (85033748923160677, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_7, prime_thirtyEightAJ_6917, prime_thirtyEightAJ_10911689, prime_thirtyEightAJ_85033748923160677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740808 : Nat.totient 44926141595907246165431740808 = 22255331750252737821741450240 := by
  rw [← show ((([(2, 3), (113, 1), (2543, 1), (113731, 1), (171832565055736069, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_113, prime_thirtyEightAJ_2543, prime_thirtyEightAJ_113731, prime_thirtyEightAJ_171832565055736069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740809 : Nat.totient 44926141595907246165431740809 = 29722129041177099476544816000 := by
  rw [← show ((([(3, 2), (131, 1), (114795281, 1), (331941292730282491, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_131, prime_thirtyEightAJ_114795281, prime_thirtyEightAJ_331941292730282491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740810 : Nat.totient 44926141595907246165431740810 = 17969357459235921030373621248 := by
  rw [← show ((([(2, 1), (5, 1), (16349, 1), (12831738653, 1), (21415214170873, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_16349, prime_thirtyEightAJ_12831738653, prime_thirtyEightAJ_21415214170873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740811 : Nat.totient 44926141595907246165431740811 = 40349875255907931933903643720 := by
  rw [← show ((([(11, 1), (83, 1), (49207164946229185285248347, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_11, prime_thirtyEightAJ_83, prime_thirtyEightAJ_49207164946229185285248347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740812 : Nat.totient 44926141595907246165431740812 = 14932471132164013052120577216 := by
  rw [← show ((([(2, 2), (3, 1), (349, 1), (10727349951267250755833749, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_349, prime_thirtyEightAJ_10727349951267250755833749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740813 : Nat.totient 44926141595907246165431740813 = 41470284550068227229629299200 := by
  rw [← show ((([(13, 1), (3455857045839018935802441601, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_13, prime_thirtyEightAJ_3455857045839018935802441601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740814 : Nat.totient 44926141595907246165431740814 = 19248965863007791882720089600 := by
  rw [← show ((([(2, 1), (7, 1), (3889, 1), (133781, 1), (619561331, 1), (9955301119, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_7, prime_thirtyEightAJ_3889, prime_thirtyEightAJ_133781, prime_thirtyEightAJ_619561331, prime_thirtyEightAJ_9955301119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740815 : Nat.totient 44926141595907246165431740815 = 23941933395884102327811709056 := by
  rw [← show ((([(3, 1), (5, 1), (1283, 1), (120893608013, 1), (19309804064599, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_1283, prime_thirtyEightAJ_120893608013, prime_thirtyEightAJ_19309804064599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740816 : Nat.totient 44926141595907246165431740816 = 22463070793002090970142112032 := by
  rw [← show ((([(2, 4), (4536589979, 1), (618941509535129819, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_4536589979, prime_thirtyEightAJ_618941509535129819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740817 : Nat.totient 44926141595907246165431740817 = 42283427384383290508641638400 := by
  rw [← show ((([(17, 1), (2642714211523955656790102401, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_17, prime_thirtyEightAJ_2642714211523955656790102401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740818 : Nat.totient 44926141595907246165431740818 = 14975086482245734984334630400 := by
  rw [← show ((([(2, 1), (3, 2), (56633, 1), (507641, 1), (158598107, 1), (547396931, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_56633, prime_thirtyEightAJ_507641, prime_thirtyEightAJ_158598107, prime_thirtyEightAJ_547396931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740819 : Nat.totient 44926141595907246165431740819 = 42561405339474935178136935936 := by
  rw [← show ((([(19, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_19, prime_thirtyEightAJ_210193, prime_thirtyEightAJ_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740820 : Nat.totient 44926141595907246165431740820 = 17970456638362898466172696320 := by
  rw [← show ((([(2, 2), (5, 1), (2246307079795362308271587041, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_2246307079795362308271587041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740821 : Nat.totient 44926141595907246165431740821 = 25646637818872719317431784448 := by
  rw [← show ((([(3, 1), (7, 1), (1009, 1), (2120257756189874282195089, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_7, prime_thirtyEightAJ_1009, prime_thirtyEightAJ_2120257756189874282195089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740822 : Nat.totient 44926141595907246165431740822 = 20320469438959065366314553600 := by
  rw [← show ((([(2, 1), (11, 1), (271, 1), (907, 1), (7477, 1), (1111149466697709529, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_11, prime_thirtyEightAJ_271, prime_thirtyEightAJ_907, prime_thirtyEightAJ_7477, prime_thirtyEightAJ_1111149466697709529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740823 : Nat.totient 44926141595907246165431740823 = 42972831048792820337369865504 := by
  rw [← show ((([(23, 1), (1000658653, 1), (1952024797181142517, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_23, prime_thirtyEightAJ_1000658653, prime_thirtyEightAJ_1952024797181142517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740824 : Nat.totient 44926141595907246165431740824 = 14975380531969082055143913600 := by
  rw [← show ((([(2, 3), (3, 1), (1871922566496135256892989201, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_1871922566496135256892989201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740825 : Nat.totient 44926141595907246165431740825 = 35867112633447099197371367760 := by
  rw [← show ((([(5, 2), (487, 1), (3690032163934886748700759, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_487, prime_thirtyEightAJ_3690032163934886748700759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740826 : Nat.totient 44926141595907246165431740826 = 20735142275030931608591696448 := by
  rw [← show ((([(2, 1), (13, 1), (6684901168709, 1), (258482284077389, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_13, prime_thirtyEightAJ_6684901168709, prime_thirtyEightAJ_258482284077389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740827 : Nat.totient 44926141595907246165431740827 = 29800254726933449717773807344 := by
  rw [← show ((([(3, 4), (199, 1), (2787154388976192453963133, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_199, prime_thirtyEightAJ_2787154388976192453963133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740828 : Nat.totient 44926141595907246165431740828 = 19254060457899161075631611904 := by
  rw [← show ((([(2, 2), (7, 1), (85171937, 1), (18838423939996660673, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_7, prime_thirtyEightAJ_85171937, prime_thirtyEightAJ_18838423939996660673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740829 : Nat.totient 44926141595907246165431740829 = 43326097044087847961442610944 := by
  rw [← show ((([(29, 1), (853, 1), (2912887, 1), (394349519, 1), (1581055589, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_29, prime_thirtyEightAJ_853, prime_thirtyEightAJ_2912887, prime_thirtyEightAJ_394349519, prime_thirtyEightAJ_1581055589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740830 : Nat.totient 44926141595907246165431740830 = 11980304425575265644115130880 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1497538053196908205514391361, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_1497538053196908205514391361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740831 : Nat.totient 44926141595907246165431740831 = 43474529054035048189716000000 := by
  rw [← show ((([(31, 1), (18251, 1), (23861595971, 1), (3327754464481, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_31, prime_thirtyEightAJ_18251, prime_thirtyEightAJ_23861595971, prime_thirtyEightAJ_3327754464481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740832 : Nat.totient 44926141595907246165431740832 = 22414970003953722390889918912 := by
  rw [← show ((([(2, 5), (467, 1), (3006299624993793239121503, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_467, prime_thirtyEightAJ_3006299624993793239121503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740833 : Nat.totient 44926141595907246165431740833 = 27227964603578592865187445840 := by
  rw [← show ((([(3, 1), (11, 1), (26561252249023, 1), (51255046916287, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_11, prime_thirtyEightAJ_26561252249023, prime_thirtyEightAJ_51255046916287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740834 : Nat.totient 44926141595907246165431740834 = 21141713692191645254320819200 := by
  rw [← show ((([(2, 1), (17, 1), (1321357105761977828395051201, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_17, prime_thirtyEightAJ_1321357105761977828395051201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740835 : Nat.totient 44926141595907246165431740835 = 30745414822515136249222454400 := by
  rw [← show ((([(5, 1), (7, 1), (823, 1), (1301, 1), (1198819905425913042347, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_7, prime_thirtyEightAJ_823, prime_thirtyEightAJ_1301, prime_thirtyEightAJ_1198819905425913042347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740836 : Nat.totient 44926141595907246165431740836 = 14961809223955841067764242560 := by
  rw [← show ((([(2, 2), (3, 2), (1439, 1), (4729, 1), (183386141468582607671, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_1439, prime_thirtyEightAJ_4729, prime_thirtyEightAJ_183386141468582607671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740837 : Nat.totient 44926141595907246165431740837 = 43059504813180966877396454352 := by
  rw [← show ((([(37, 1), (67, 1), (18122687210934750369274603, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_37, prime_thirtyEightAJ_67, prime_thirtyEightAJ_18122687210934750369274603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740838 : Nat.totient 44926141595907246165431740838 = 21069986901359321511017571456 := by
  rw [← show ((([(2, 1), (19, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_19, prime_thirtyEightAJ_103, prime_thirtyEightAJ_5009, prime_thirtyEightAJ_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740839 : Nat.totient 44926141595907246165431740839 = 27601328667889714236160020480 := by
  rw [← show ((([(3, 1), (13, 1), (661, 1), (7457, 1), (233705488596142099613, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_13, prime_thirtyEightAJ_661, prime_thirtyEightAJ_7457, prime_thirtyEightAJ_233705488596142099613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740840 : Nat.totient 44926141595907246165431740840 = 17970456637328293467187126272 := by
  rw [← show ((([(2, 3), (5, 1), (17369393617, 1), (64662795067204513, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_17369393617, prime_thirtyEightAJ_64662795067204513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740841 : Nat.totient 44926141595907246165431740841 = 43213052713759834041905059200 := by
  rw [← show ((([(41, 1), (71, 1), (6696342859, 1), (2304725644927109, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_41, prime_thirtyEightAJ_71, prime_thirtyEightAJ_6696342859, prime_thirtyEightAJ_2304725644927109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740842 : Nat.totient 44926141595907246165431740842 = 12835891031151828258459649584 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (85903, 1), (12452068472553829032367, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_7, prime_thirtyEightAJ_85903, prime_thirtyEightAJ_12452068472553829032367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740843 : Nat.totient 44926141595907246165431740843 = 43845467517320038452806023464 := by
  rw [← show ((([(43, 1), (1223, 1), (854287809159847994170487, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_43, prime_thirtyEightAJ_1223, prime_thirtyEightAJ_854287809159847994170487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740844 : Nat.totient 44926141595907246165431740844 = 20290903558082022008706831840 := by
  rw [← show ((([(2, 2), (11, 2), (157, 1), (591226793650408566687263, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_11, prime_thirtyEightAJ_157, prime_thirtyEightAJ_591226793650408566687263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740845 : Nat.totient 44926141595907246165431740845 = 23949127965261144354215726688 := by
  rw [← show ((([(3, 2), (5, 1), (2087, 1), (478370245391122250603543, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_2087, prime_thirtyEightAJ_478370245391122250603543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740846 : Nat.totient 44926141595907246165431740846 = 21464557541236842222675787104 := by
  rw [← show ((([(2, 1), (23, 1), (983, 1), (7016656643, 1), (141598139481229, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_23, prime_thirtyEightAJ_983, prime_thirtyEightAJ_7016656643, prime_thirtyEightAJ_141598139481229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740847 : Nat.totient 44926141595907246165431740847 = 43970255407379708740271525400 := by
  rw [← show ((([(47, 1), (4058011, 1), (235552676694175913491, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_47, prime_thirtyEightAJ_4058011, prime_thirtyEightAJ_235552676694175913491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740848 : Nat.totient 44926141595907246165431740848 = 14975366167412585969110852672 := by
  rw [← show ((([(2, 4), (3, 1), (1042523, 1), (897784781005376023787, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_1042523, prime_thirtyEightAJ_897784781005376023787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740849 : Nat.totient 44926141595907246165431740849 = 38508121367920496713227206400 := by
  rw [← show ((([(7, 2), (916860032569535636029219201, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_7, prime_thirtyEightAJ_916860032569535636029219201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740850 : Nat.totient 44926141595907246165431740850 = 17945462957363784560100119120 := by
  rw [← show ((([(2, 1), (5, 2), (719, 1), (1249684049955695303628143, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_719, prime_thirtyEightAJ_1249684049955695303628143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740851 : Nat.totient 44926141595907246165431740851 = 28188949386861863412001071104 := by
  rw [← show ((([(3, 1), (17, 1), (12797297, 1), (68835218653958870033, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_17, prime_thirtyEightAJ_12797297, prime_thirtyEightAJ_68835218653958870033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740852 : Nat.totient 44926141595907246165431740852 = 20451098814043349462738289408 := by
  rw [← show ((([(2, 2), (13, 1), (73, 1), (49146259, 1), (240814399918246243, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_13, prime_thirtyEightAJ_73, prime_thirtyEightAJ_49146259, prime_thirtyEightAJ_240814399918246243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740853 : Nat.totient 44926141595907246165431740853 = 43520523117814167694901251776 := by
  rw [← show ((([(53, 1), (79, 1), (9738312517, 1), (1101824571111907, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_53, prime_thirtyEightAJ_79, prime_thirtyEightAJ_9738312517, prime_thirtyEightAJ_1101824571111907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740854 : Nat.totient 44926141595907246165431740854 = 14975380531832849657057025000 := by
  rw [← show ((([(2, 1), (3, 3), (109926847451, 1), (7568356633535251, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_109926847451, prime_thirtyEightAJ_7568356633535251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740855 : Nat.totient 44926141595907246165431740855 = 32477906423304262733243376000 := by
  rw [← show ((([(5, 1), (11, 1), (167, 1), (30757451, 1), (159026543727295333, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_11, prime_thirtyEightAJ_167, prime_thirtyEightAJ_30757451, prime_thirtyEightAJ_159026543727295333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740856 : Nat.totient 44926141595907246165431740856 = 19193321603697834789695802240 := by
  rw [← show ((([(2, 3), (7, 1), (317, 1), (26713663, 1), (94736729819765531, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_7, prime_thirtyEightAJ_317, prime_thirtyEightAJ_26713663, prime_thirtyEightAJ_94736729819765531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740857 : Nat.totient 44926141595907246165431740857 = 28287895126696180418596608000 := by
  rw [← show ((([(3, 1), (19, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_19, prime_thirtyEightAJ_421, prime_thirtyEightAJ_1483, prime_thirtyEightAJ_2072201, prime_thirtyEightAJ_2567179, prime_thirtyEightAJ_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740858 : Nat.totient 44926141595907246165431740858 = 21647000232688610344169041920 := by
  rw [← show ((([(2, 1), (29, 1), (523, 1), (1725697, 1), (858232378305983971, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_29, prime_thirtyEightAJ_523, prime_thirtyEightAJ_1725697, prime_thirtyEightAJ_858232378305983971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740859 : Nat.totient 44926141595907246165431740859 = 44046979268761911156810120480 := by
  rw [← show ((([(59, 1), (443, 1), (2447, 1), (702440291331326015581, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_59, prime_thirtyEightAJ_443, prime_thirtyEightAJ_2447, prime_thirtyEightAJ_702440291331326015581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740860 : Nat.totient 44926141595907246165431740860 = 11980165130546826216244192512 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (86183, 1), (42041059, 1), (206658187604573, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_86183, prime_thirtyEightAJ_42041059, prime_thirtyEightAJ_206658187604573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740861 : Nat.totient 44926141595907246165431740861 = 44189646870814805725496082240 := by
  rw [← show ((([(61, 1), (73579589, 1), (10009489513770858509, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_61, prime_thirtyEightAJ_73579589, prime_thirtyEightAJ_10009489513770858509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740862 : Nat.totient 44926141595907246165431740862 = 21738455610922861047789552000 := by
  rw [← show ((([(2, 1), (31, 1), (724615187030762034926318401, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_31, prime_thirtyEightAJ_724615187030762034926318401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740863 : Nat.totient 44926141595907246165431740863 = 25499473817737091791450664448 := by
  rw [← show ((([(3, 2), (7, 1), (149, 1), (81929, 1), (7204737367, 1), (8108051443, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_7, prime_thirtyEightAJ_149, prime_thirtyEightAJ_81929, prime_thirtyEightAJ_7204737367, prime_thirtyEightAJ_8108051443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740864 : Nat.totient 44926141595907246165431740864 = 22463046307647127455207229440 := by
  rw [← show ((([(2, 6), (1318411, 1), (3014237, 1), (176640763490393, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_1318411, prime_thirtyEightAJ_3014237, prime_thirtyEightAJ_176640763490393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740865 : Nat.totient 44926141595907246165431740865 = 33147173464768256931889632000 := by
  rw [← show ((([(5, 1), (13, 1), (1151, 1), (145031, 1), (18499207, 1), (223818761263, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_13, prime_thirtyEightAJ_1151, prime_thirtyEightAJ_145031, prime_thirtyEightAJ_18499207, prime_thirtyEightAJ_223818761263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740866 : Nat.totient 44926141595907246165431740866 = 13613982301790074595585376000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (680699115089503729779268801, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_11, prime_thirtyEightAJ_680699115089503729779268801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740867 : Nat.totient 44926141595907246165431740867 = 44925330244218980755738752000 := by
  rw [← show ((([(64033, 1), (443909, 1), (5261701, 1), (300382866011, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_64033, prime_thirtyEightAJ_443909, prime_thirtyEightAJ_5261701, prime_thirtyEightAJ_300382866011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740868 : Nat.totient 44926141595907246165431740868 = 21113785403785594431610675200 := by
  rw [← show ((([(2, 2), (17, 1), (757, 1), (25340904301, 1), (34440719883793, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_17, prime_thirtyEightAJ_757, prime_thirtyEightAJ_25340904301, prime_thirtyEightAJ_34440719883793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740869 : Nat.totient 44926141595907246165431740869 = 28647431600865129554587918448 := by
  rw [← show ((([(3, 1), (23, 1), (25523, 1), (25510461207144931604987, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_23, prime_thirtyEightAJ_25523, prime_thirtyEightAJ_25510461207144931604987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740870 : Nat.totient 44926141595907246165431740870 = 15384623095478757090750003168 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (827, 1), (776060487060066439202483, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_7, prime_thirtyEightAJ_827, prime_thirtyEightAJ_776060487060066439202483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740871 : Nat.totient 44926141595907246165431740871 = 44693363270185013368862277120 := by
  rw [← show ((([(193, 1), (114600677, 1), (2031209080292687611, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_193, prime_thirtyEightAJ_114600677, prime_thirtyEightAJ_2031209080292687611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740872 : Nat.totient 44926141595907246165431740872 = 14975380520770296551086174848 := by
  rw [← show ((([(2, 3), (3, 2), (1337232557, 1), (466616061331839893, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_1337232557, prime_thirtyEightAJ_466616061331839893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740873 : Nat.totient 44926141595907246165431740873 = 44926141595907246165431740872 := by
  rw [← show ((([(44926141595907246165431740873, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_44926141595907246165431740873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740874 : Nat.totient 44926141595907246165431740874 = 21793423368251338655247273600 := by
  rw [← show ((([(2, 1), (37, 1), (359, 1), (13151, 1), (128592066474141292489, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_37, prime_thirtyEightAJ_359, prime_thirtyEightAJ_13151, prime_thirtyEightAJ_128592066474141292489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740875 : Nat.totient 44926141595907246165431740875 = 23734395033944585301370368000 := by
  rw [← show ((([(3, 1), (5, 3), (137, 1), (541, 1), (3229, 1), (500589777363894013, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_137, prime_thirtyEightAJ_541, prime_thirtyEightAJ_3229, prime_thirtyEightAJ_500589777363894013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740876 : Nat.totient 44926141595907246165431740876 = 21280803896444840833759419600 := by
  rw [← show ((([(2, 2), (19, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_19, prime_thirtyEightAJ_1222615931, prime_thirtyEightAJ_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740877 : Nat.totient 44926141595907246165431740877 = 34660775307968285393385000000 := by
  rw [← show ((([(7, 1), (11, 1), (101, 1), (50180173151, 1), (115121083129651, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_7, prime_thirtyEightAJ_11, prime_thirtyEightAJ_101, prime_thirtyEightAJ_50180173151, prime_thirtyEightAJ_115121083129651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740878 : Nat.totient 44926141595907246165431740878 = 13584255337555953387688251648 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (89, 1), (163, 1), (39703327656062808021443, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_13, prime_thirtyEightAJ_89, prime_thirtyEightAJ_163, prime_thirtyEightAJ_39703327656062808021443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740879 : Nat.totient 44926141595907246165431740879 = 44926141296624714996126292056 := by
  rw [← show ((([(154228859, 1), (6420810587, 1), (45367371463, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_154228859, prime_thirtyEightAJ_6420810587, prime_thirtyEightAJ_45367371463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740880 : Nat.totient 44926141595907246165431740880 = 17866581166464847029952039424 := by
  rw [← show ((([(2, 4), (5, 1), (173, 1), (3246108496814107381895357, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_173, prime_thirtyEightAJ_3246108496814107381895357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740881 : Nat.totient 44926141595907246165431740881 = 29950747704924777363852145584 := by
  rw [← show ((([(3, 3), (2241989, 1), (742167410374799740327, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_2241989, prime_thirtyEightAJ_742167410374799740327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740882 : Nat.totient 44926141595907246165431740882 = 21657223904570903426991083520 := by
  rw [← show ((([(2, 1), (41, 1), (97, 1), (677, 1), (8343050382369831510029, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_41, prime_thirtyEightAJ_97, prime_thirtyEightAJ_677, prime_thirtyEightAJ_8343050382369831510029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740883 : Nat.totient 44926141595907246165431740883 = 44926141595907246165431740882 := by
  rw [← show ((([(44926141595907246165431740883, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_44926141595907246165431740883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740884 : Nat.totient 44926141595907246165431740884 = 12836040228707282494581915648 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (59767193, 1), (1189299689, 1), (7524292513, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_7, prime_thirtyEightAJ_59767193, prime_thirtyEightAJ_1189299689, prime_thirtyEightAJ_7524292513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740885 : Nat.totient 44926141595907246165431740885 = 33826741907506632406913310720 := by
  rw [← show ((([(5, 1), (17, 1), (528542842304791131358020481, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_17, prime_thirtyEightAJ_528542842304791131358020481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740886 : Nat.totient 44926141595907246165431740886 = 21940338414489889543099713504 := by
  rw [← show ((([(2, 1), (43, 1), (65419, 1), (17671339223, 1), (451884354773, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_43, prime_thirtyEightAJ_65419, prime_thirtyEightAJ_17671339223, prime_thirtyEightAJ_451884354773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740887 : Nat.totient 44926141595907246165431740887 = 28917976047185142871181682272 := by
  rw [← show ((([(3, 1), (29, 1), (189651827, 1), (2722844489849627963, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_29, prime_thirtyEightAJ_189651827, prime_thirtyEightAJ_2722844489849627963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740888 : Nat.totient 44926141595907246165431740888 = 20419768627075268920988121600 := by
  rw [← show ((([(2, 3), (11, 1), (17419, 1), (628561, 1), (46627893857328739, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_11, prime_thirtyEightAJ_17419, prime_thirtyEightAJ_628561, prime_thirtyEightAJ_46627893857328739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740889 : Nat.totient 44926141595907246165431740889 = 44572388113317507814530197136 := by
  rw [← show ((([(127, 1), (10279219, 1), (34414010094002910653, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_127, prime_thirtyEightAJ_10279219, prime_thirtyEightAJ_34414010094002910653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740890 : Nat.totient 44926141595907246165431740890 = 11980300312718167463829880800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (2912891, 1), (171369045757508972531, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_5, prime_thirtyEightAJ_2912891, prime_thirtyEightAJ_171369045757508972531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740891 : Nat.totient 44926141595907246165431740891 = 35545958185772766196825113600 := by
  rw [← show ((([(7, 1), (13, 1), (493693863691288419400348801, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_7, prime_thirtyEightAJ_13, prime_thirtyEightAJ_493693863691288419400348801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740892 : Nat.totient 44926141595907246165431740892 = 21485376600737637991114208640 := by
  rw [← show ((([(2, 2), (23, 1), (20681, 1), (58384288267, 1), (404430377963, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_23, prime_thirtyEightAJ_20681, prime_thirtyEightAJ_58384288267, prime_thirtyEightAJ_404430377963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740893 : Nat.totient 44926141595907246165431740893 = 28976424964909038161955172800 := by
  rw [← show ((([(3, 1), (31, 1), (3547, 1), (2650463, 1), (51384630581148941, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_31, prime_thirtyEightAJ_3547, prime_thirtyEightAJ_2650463, prime_thirtyEightAJ_51384630581148941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740894 : Nat.totient 44926141595907246165431740894 = 21437890379779514011923087360 := by
  rw [← show ((([(2, 1), (47, 1), (83, 1), (179, 1), (229, 1), (353, 1), (3709, 1), (107293428600521, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_47, prime_thirtyEightAJ_83, prime_thirtyEightAJ_179, prime_thirtyEightAJ_229, prime_thirtyEightAJ_353, prime_thirtyEightAJ_3709, prime_thirtyEightAJ_107293428600521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740895 : Nat.totient 44926141595907246165431740895 = 33898956612756293131155686016 := by
  rw [← show ((([(5, 1), (19, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_5, prime_thirtyEightAJ_19, prime_thirtyEightAJ_239, prime_thirtyEightAJ_4327, prime_thirtyEightAJ_1214459, prime_thirtyEightAJ_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740896 : Nat.totient 44926141595907246165431740896 = 14975380513048878226421535744 := by
  rw [← show ((([(2, 5), (3, 1), (791502073, 1), (591256368856072237, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_3, prime_thirtyEightAJ_791502073, prime_thirtyEightAJ_591256368856072237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740897 : Nat.totient 44926141595907246165431740897 = 44926141595821102274073159940 := by
  rw [← show ((([(521527561367, 1), (86143369831019591, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_521527561367, prime_thirtyEightAJ_86143369831019591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740898 : Nat.totient 44926141595907246165431740898 = 19241059967765811997156003200 := by
  rw [← show ((([(2, 1), (7, 2), (1481, 1), (309540861772294272798521, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_7, prime_thirtyEightAJ_1481, prime_thirtyEightAJ_309540861772294272798521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740899 : Nat.totient 44926141595907246165431740899 = 27094155288829853395109207040 := by
  rw [← show ((([(3, 2), (11, 1), (383, 1), (433, 1), (380903827, 1), (7183927164917, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_3, prime_thirtyEightAJ_11, prime_thirtyEightAJ_383, prime_thirtyEightAJ_433, prime_thirtyEightAJ_380903827, prime_thirtyEightAJ_7183927164917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyEightAJ_44926141595907246165431740900 : Nat.totient 44926141595907246165431740900 = 17970222466352799926295027840 := by
  rw [← show ((([(2, 2), (5, 2), (77587, 1), (7032919, 1), (823331149041853, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907246165431740900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyEightAJ_2, prime_thirtyEightAJ_5, prime_thirtyEightAJ_77587, prime_thirtyEightAJ_7032919, prime_thirtyEightAJ_823331149041853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyEightAJ : certifiedKill 1 44926141595907246165431740799 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyEightAJ_44926141595907246165431740800, phi_thirtyEightAJ_44926141595907246165431740801, phi_thirtyEightAJ_44926141595907246165431740802,
    phi_thirtyEightAJ_44926141595907246165431740803, phi_thirtyEightAJ_44926141595907246165431740804, phi_thirtyEightAJ_44926141595907246165431740805,
    phi_thirtyEightAJ_44926141595907246165431740806, phi_thirtyEightAJ_44926141595907246165431740807, phi_thirtyEightAJ_44926141595907246165431740808,
    phi_thirtyEightAJ_44926141595907246165431740809, phi_thirtyEightAJ_44926141595907246165431740810, phi_thirtyEightAJ_44926141595907246165431740811,
    phi_thirtyEightAJ_44926141595907246165431740812, phi_thirtyEightAJ_44926141595907246165431740813, phi_thirtyEightAJ_44926141595907246165431740814,
    phi_thirtyEightAJ_44926141595907246165431740815, phi_thirtyEightAJ_44926141595907246165431740816, phi_thirtyEightAJ_44926141595907246165431740817,
    phi_thirtyEightAJ_44926141595907246165431740818, phi_thirtyEightAJ_44926141595907246165431740819, phi_thirtyEightAJ_44926141595907246165431740820,
    phi_thirtyEightAJ_44926141595907246165431740821, phi_thirtyEightAJ_44926141595907246165431740822, phi_thirtyEightAJ_44926141595907246165431740823,
    phi_thirtyEightAJ_44926141595907246165431740824, phi_thirtyEightAJ_44926141595907246165431740825, phi_thirtyEightAJ_44926141595907246165431740826,
    phi_thirtyEightAJ_44926141595907246165431740827, phi_thirtyEightAJ_44926141595907246165431740828, phi_thirtyEightAJ_44926141595907246165431740829,
    phi_thirtyEightAJ_44926141595907246165431740830, phi_thirtyEightAJ_44926141595907246165431740831, phi_thirtyEightAJ_44926141595907246165431740832,
    phi_thirtyEightAJ_44926141595907246165431740833, phi_thirtyEightAJ_44926141595907246165431740834, phi_thirtyEightAJ_44926141595907246165431740835,
    phi_thirtyEightAJ_44926141595907246165431740836, phi_thirtyEightAJ_44926141595907246165431740837, phi_thirtyEightAJ_44926141595907246165431740838,
    phi_thirtyEightAJ_44926141595907246165431740839, phi_thirtyEightAJ_44926141595907246165431740840, phi_thirtyEightAJ_44926141595907246165431740841,
    phi_thirtyEightAJ_44926141595907246165431740842, phi_thirtyEightAJ_44926141595907246165431740843, phi_thirtyEightAJ_44926141595907246165431740844,
    phi_thirtyEightAJ_44926141595907246165431740845, phi_thirtyEightAJ_44926141595907246165431740846, phi_thirtyEightAJ_44926141595907246165431740847,
    phi_thirtyEightAJ_44926141595907246165431740848, phi_thirtyEightAJ_44926141595907246165431740849, phi_thirtyEightAJ_44926141595907246165431740850,
    phi_thirtyEightAJ_44926141595907246165431740851, phi_thirtyEightAJ_44926141595907246165431740852, phi_thirtyEightAJ_44926141595907246165431740853,
    phi_thirtyEightAJ_44926141595907246165431740854, phi_thirtyEightAJ_44926141595907246165431740855, phi_thirtyEightAJ_44926141595907246165431740856,
    phi_thirtyEightAJ_44926141595907246165431740857, phi_thirtyEightAJ_44926141595907246165431740858, phi_thirtyEightAJ_44926141595907246165431740859,
    phi_thirtyEightAJ_44926141595907246165431740860, phi_thirtyEightAJ_44926141595907246165431740861, phi_thirtyEightAJ_44926141595907246165431740862,
    phi_thirtyEightAJ_44926141595907246165431740863, phi_thirtyEightAJ_44926141595907246165431740864, phi_thirtyEightAJ_44926141595907246165431740865,
    phi_thirtyEightAJ_44926141595907246165431740866, phi_thirtyEightAJ_44926141595907246165431740867, phi_thirtyEightAJ_44926141595907246165431740868,
    phi_thirtyEightAJ_44926141595907246165431740869, phi_thirtyEightAJ_44926141595907246165431740870, phi_thirtyEightAJ_44926141595907246165431740871,
    phi_thirtyEightAJ_44926141595907246165431740872, phi_thirtyEightAJ_44926141595907246165431740873, phi_thirtyEightAJ_44926141595907246165431740874,
    phi_thirtyEightAJ_44926141595907246165431740875, phi_thirtyEightAJ_44926141595907246165431740876, phi_thirtyEightAJ_44926141595907246165431740877,
    phi_thirtyEightAJ_44926141595907246165431740878, phi_thirtyEightAJ_44926141595907246165431740879, phi_thirtyEightAJ_44926141595907246165431740880,
    phi_thirtyEightAJ_44926141595907246165431740881, phi_thirtyEightAJ_44926141595907246165431740882, phi_thirtyEightAJ_44926141595907246165431740883,
    phi_thirtyEightAJ_44926141595907246165431740884, phi_thirtyEightAJ_44926141595907246165431740885, phi_thirtyEightAJ_44926141595907246165431740886,
    phi_thirtyEightAJ_44926141595907246165431740887, phi_thirtyEightAJ_44926141595907246165431740888, phi_thirtyEightAJ_44926141595907246165431740889,
    phi_thirtyEightAJ_44926141595907246165431740890, phi_thirtyEightAJ_44926141595907246165431740891, phi_thirtyEightAJ_44926141595907246165431740892,
    phi_thirtyEightAJ_44926141595907246165431740893, phi_thirtyEightAJ_44926141595907246165431740894, phi_thirtyEightAJ_44926141595907246165431740895,
    phi_thirtyEightAJ_44926141595907246165431740896, phi_thirtyEightAJ_44926141595907246165431740897, phi_thirtyEightAJ_44926141595907246165431740898,
    phi_thirtyEightAJ_44926141595907246165431740899, phi_thirtyEightAJ_44926141595907246165431740900]

end TotientTailPeriodKiller
end Erdos249257
