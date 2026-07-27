import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def nineteenQFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem nineteenQFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    nineteenQFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [nineteenQFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [nineteenQFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then nineteenQFastPow a n * nineteenQFastPow a n * a
        else nineteenQFastPow a n * nineteenQFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_nineteenQ_2 : Nat.Prime 2 := by norm_num
private theorem prime_nineteenQ_3 : Nat.Prime 3 := by norm_num
private theorem prime_nineteenQ_5 : Nat.Prime 5 := by norm_num
private theorem prime_nineteenQ_7 : Nat.Prime 7 := by norm_num
private theorem prime_nineteenQ_11 : Nat.Prime 11 := by norm_num
private theorem prime_nineteenQ_13 : Nat.Prime 13 := by norm_num
private theorem prime_nineteenQ_17 : Nat.Prime 17 := by norm_num
private theorem prime_nineteenQ_19 : Nat.Prime 19 := by norm_num
private theorem prime_nineteenQ_23 : Nat.Prime 23 := by norm_num
private theorem prime_nineteenQ_29 : Nat.Prime 29 := by norm_num
private theorem prime_nineteenQ_31 : Nat.Prime 31 := by norm_num
private theorem prime_nineteenQ_37 : Nat.Prime 37 := by norm_num
private theorem prime_nineteenQ_41 : Nat.Prime 41 := by norm_num
private theorem prime_nineteenQ_43 : Nat.Prime 43 := by norm_num
private theorem prime_nineteenQ_47 : Nat.Prime 47 := by norm_num
private theorem prime_nineteenQ_53 : Nat.Prime 53 := by norm_num
private theorem prime_nineteenQ_59 : Nat.Prime 59 := by norm_num
private theorem prime_nineteenQ_61 : Nat.Prime 61 := by norm_num
private theorem prime_nineteenQ_67 : Nat.Prime 67 := by norm_num
private theorem prime_nineteenQ_71 : Nat.Prime 71 := by norm_num
private theorem prime_nineteenQ_73 : Nat.Prime 73 := by norm_num
private theorem prime_nineteenQ_79 : Nat.Prime 79 := by norm_num
private theorem prime_nineteenQ_83 : Nat.Prime 83 := by norm_num
private theorem prime_nineteenQ_89 : Nat.Prime 89 := by norm_num
private theorem prime_nineteenQ_97 : Nat.Prime 97 := by norm_num
private theorem prime_nineteenQ_101 : Nat.Prime 101 := by norm_num
private theorem prime_nineteenQ_103 : Nat.Prime 103 := by norm_num
private theorem prime_nineteenQ_107 : Nat.Prime 107 := by norm_num
private theorem prime_nineteenQ_109 : Nat.Prime 109 := by norm_num
private theorem prime_nineteenQ_113 : Nat.Prime 113 := by norm_num
private theorem prime_nineteenQ_127 : Nat.Prime 127 := by norm_num
private theorem prime_nineteenQ_131 : Nat.Prime 131 := by norm_num
private theorem prime_nineteenQ_137 : Nat.Prime 137 := by norm_num
private theorem prime_nineteenQ_139 : Nat.Prime 139 := by norm_num
private theorem prime_nineteenQ_149 : Nat.Prime 149 := by norm_num
private theorem prime_nineteenQ_151 : Nat.Prime 151 := by norm_num
private theorem prime_nineteenQ_157 : Nat.Prime 157 := by norm_num
private theorem prime_nineteenQ_163 : Nat.Prime 163 := by norm_num
private theorem prime_nineteenQ_173 : Nat.Prime 173 := by norm_num
private theorem prime_nineteenQ_179 : Nat.Prime 179 := by norm_num
private theorem prime_nineteenQ_181 : Nat.Prime 181 := by norm_num
private theorem prime_nineteenQ_191 : Nat.Prime 191 := by norm_num
private theorem prime_nineteenQ_193 : Nat.Prime 193 := by norm_num
private theorem prime_nineteenQ_197 : Nat.Prime 197 := by norm_num
private theorem prime_nineteenQ_211 : Nat.Prime 211 := by norm_num
private theorem prime_nineteenQ_223 : Nat.Prime 223 := by norm_num
private theorem prime_nineteenQ_229 : Nat.Prime 229 := by norm_num
private theorem prime_nineteenQ_233 : Nat.Prime 233 := by norm_num
private theorem prime_nineteenQ_239 : Nat.Prime 239 := by norm_num
private theorem prime_nineteenQ_251 : Nat.Prime 251 := by norm_num
private theorem prime_nineteenQ_269 : Nat.Prime 269 := by norm_num
private theorem prime_nineteenQ_271 : Nat.Prime 271 := by norm_num
private theorem prime_nineteenQ_277 : Nat.Prime 277 := by norm_num
private theorem prime_nineteenQ_283 : Nat.Prime 283 := by norm_num
private theorem prime_nineteenQ_307 : Nat.Prime 307 := by norm_num
private theorem prime_nineteenQ_311 : Nat.Prime 311 := by norm_num
private theorem prime_nineteenQ_317 : Nat.Prime 317 := by norm_num
private theorem prime_nineteenQ_331 : Nat.Prime 331 := by norm_num
private theorem prime_nineteenQ_337 : Nat.Prime 337 := by norm_num
private theorem prime_nineteenQ_347 : Nat.Prime 347 := by norm_num
private theorem prime_nineteenQ_349 : Nat.Prime 349 := by norm_num
private theorem prime_nineteenQ_353 : Nat.Prime 353 := by norm_num
private theorem prime_nineteenQ_359 : Nat.Prime 359 := by norm_num
private theorem prime_nineteenQ_367 : Nat.Prime 367 := by norm_num
private theorem prime_nineteenQ_373 : Nat.Prime 373 := by norm_num
private theorem prime_nineteenQ_379 : Nat.Prime 379 := by norm_num
private theorem prime_nineteenQ_389 : Nat.Prime 389 := by norm_num
private theorem prime_nineteenQ_397 : Nat.Prime 397 := by norm_num
private theorem prime_nineteenQ_409 : Nat.Prime 409 := by norm_num
private theorem prime_nineteenQ_419 : Nat.Prime 419 := by norm_num
private theorem prime_nineteenQ_443 : Nat.Prime 443 := by norm_num
private theorem prime_nineteenQ_449 : Nat.Prime 449 := by norm_num
private theorem prime_nineteenQ_457 : Nat.Prime 457 := by norm_num
private theorem prime_nineteenQ_461 : Nat.Prime 461 := by norm_num
private theorem prime_nineteenQ_467 : Nat.Prime 467 := by norm_num
private theorem prime_nineteenQ_479 : Nat.Prime 479 := by norm_num
private theorem prime_nineteenQ_487 : Nat.Prime 487 := by norm_num
private theorem prime_nineteenQ_499 : Nat.Prime 499 := by norm_num
private theorem prime_nineteenQ_503 : Nat.Prime 503 := by norm_num
private theorem prime_nineteenQ_509 : Nat.Prime 509 := by norm_num
private theorem prime_nineteenQ_523 : Nat.Prime 523 := by norm_num
private theorem prime_nineteenQ_577 : Nat.Prime 577 := by norm_num
private theorem prime_nineteenQ_593 : Nat.Prime 593 := by norm_num
private theorem prime_nineteenQ_601 : Nat.Prime 601 := by norm_num
private theorem prime_nineteenQ_617 : Nat.Prime 617 := by norm_num
private theorem prime_nineteenQ_631 : Nat.Prime 631 := by norm_num
private theorem prime_nineteenQ_641 : Nat.Prime 641 := by norm_num
private theorem prime_nineteenQ_653 : Nat.Prime 653 := by norm_num
private theorem prime_nineteenQ_677 : Nat.Prime 677 := by norm_num
private theorem prime_nineteenQ_691 : Nat.Prime 691 := by norm_num
private theorem prime_nineteenQ_709 : Nat.Prime 709 := by norm_num
private theorem prime_nineteenQ_719 : Nat.Prime 719 := by norm_num
private theorem prime_nineteenQ_733 : Nat.Prime 733 := by norm_num
private theorem prime_nineteenQ_743 : Nat.Prime 743 := by norm_num
private theorem prime_nineteenQ_757 : Nat.Prime 757 := by norm_num
private theorem prime_nineteenQ_769 : Nat.Prime 769 := by norm_num
private theorem prime_nineteenQ_773 : Nat.Prime 773 := by norm_num
private theorem prime_nineteenQ_827 : Nat.Prime 827 := by norm_num
private theorem prime_nineteenQ_829 : Nat.Prime 829 := by norm_num
private theorem prime_nineteenQ_839 : Nat.Prime 839 := by norm_num
private theorem prime_nineteenQ_857 : Nat.Prime 857 := by norm_num
private theorem prime_nineteenQ_859 : Nat.Prime 859 := by norm_num
private theorem prime_nineteenQ_863 : Nat.Prime 863 := by norm_num
private theorem prime_nineteenQ_907 : Nat.Prime 907 := by norm_num
private theorem prime_nineteenQ_911 : Nat.Prime 911 := by norm_num
private theorem prime_nineteenQ_953 : Nat.Prime 953 := by norm_num
private theorem prime_nineteenQ_983 : Nat.Prime 983 := by norm_num
private theorem prime_nineteenQ_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_nineteenQ_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_nineteenQ_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_nineteenQ_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_nineteenQ_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_nineteenQ_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_nineteenQ_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_nineteenQ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_nineteenQ_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_nineteenQ_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_nineteenQ_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_nineteenQ_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_nineteenQ_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_nineteenQ_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_nineteenQ_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_nineteenQ_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_nineteenQ_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_nineteenQ_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_nineteenQ_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_nineteenQ_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_nineteenQ_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_nineteenQ_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_nineteenQ_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_nineteenQ_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_nineteenQ_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_nineteenQ_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_nineteenQ_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_nineteenQ_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_nineteenQ_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_nineteenQ_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_nineteenQ_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_nineteenQ_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_nineteenQ_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_nineteenQ_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_nineteenQ_2543 : Nat.Prime 2543 := by norm_num
private theorem prime_nineteenQ_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_nineteenQ_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_nineteenQ_2671 : Nat.Prime 2671 := by norm_num
private theorem prime_nineteenQ_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_nineteenQ_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_nineteenQ_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_nineteenQ_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_nineteenQ_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_nineteenQ_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_nineteenQ_3359 : Nat.Prime 3359 := by norm_num
private theorem prime_nineteenQ_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_nineteenQ_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_nineteenQ_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_nineteenQ_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_nineteenQ_3767 : Nat.Prime 3767 := by norm_num
private theorem prime_nineteenQ_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_nineteenQ_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_nineteenQ_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_nineteenQ_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_nineteenQ_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_nineteenQ_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_nineteenQ_4729 : Nat.Prime 4729 := by norm_num
private theorem prime_nineteenQ_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_nineteenQ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_nineteenQ_5261 : Nat.Prime 5261 := by norm_num
private theorem prime_nineteenQ_5309 : Nat.Prime 5309 := by norm_num
private theorem prime_nineteenQ_5849 : Nat.Prime 5849 := by norm_num
private theorem prime_nineteenQ_6143 : Nat.Prime 6143 := by norm_num
private theorem prime_nineteenQ_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_nineteenQ_6469 : Nat.Prime 6469 := by norm_num
private theorem prime_nineteenQ_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_nineteenQ_6637 : Nat.Prime 6637 := by norm_num
private theorem prime_nineteenQ_6719 : Nat.Prime 6719 := by norm_num
private theorem prime_nineteenQ_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_nineteenQ_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_nineteenQ_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_nineteenQ_8147 : Nat.Prime 8147 := by norm_num
private theorem prime_nineteenQ_8387 : Nat.Prime 8387 := by norm_num
private theorem prime_nineteenQ_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_nineteenQ_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_nineteenQ_9007 : Nat.Prime 9007 := by norm_num
private theorem prime_nineteenQ_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_nineteenQ_9433 : Nat.Prime 9433 := by norm_num
private theorem prime_nineteenQ_9901 : Nat.Prime 9901 := by norm_num
private theorem prime_nineteenQ_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_nineteenQ_10067 : Nat.Prime 10067 := by norm_num
private theorem prime_nineteenQ_10253 : Nat.Prime 10253 := by norm_num
private theorem prime_nineteenQ_11071 : Nat.Prime 11071 := by norm_num
private theorem prime_nineteenQ_12487 : Nat.Prime 12487 := by norm_num
private theorem prime_nineteenQ_13009 : Nat.Prime 13009 := by norm_num
private theorem prime_nineteenQ_13151 : Nat.Prime 13151 := by norm_num
private theorem prime_nineteenQ_13163 : Nat.Prime 13163 := by norm_num
private theorem prime_nineteenQ_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_nineteenQ_14293 : Nat.Prime 14293 := by norm_num
private theorem prime_nineteenQ_14321 : Nat.Prime 14321 := by norm_num
private theorem prime_nineteenQ_14759 : Nat.Prime 14759 := by norm_num
private theorem prime_nineteenQ_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_nineteenQ_16333 : Nat.Prime 16333 := by norm_num
private theorem prime_nineteenQ_16349 : Nat.Prime 16349 := by norm_num
private theorem prime_nineteenQ_17137 : Nat.Prime 17137 := by norm_num
private theorem prime_nineteenQ_17419 : Nat.Prime 17419 := by norm_num
private theorem prime_nineteenQ_17923 : Nat.Prime 17923 := by norm_num
private theorem prime_nineteenQ_17959 : Nat.Prime 17959 := by norm_num
private theorem prime_nineteenQ_18233 : Nat.Prime 18233 := by norm_num
private theorem prime_nineteenQ_18341 : Nat.Prime 18341 := by norm_num
private theorem prime_nineteenQ_19489 : Nat.Prime 19489 := by norm_num
private theorem prime_nineteenQ_20681 : Nat.Prime 20681 := by norm_num
private theorem prime_nineteenQ_21191 : Nat.Prime 21191 := by norm_num
private theorem prime_nineteenQ_21481 : Nat.Prime 21481 := by norm_num
private theorem prime_nineteenQ_23041 : Nat.Prime 23041 := by norm_num
private theorem prime_nineteenQ_23369 : Nat.Prime 23369 := by norm_num
private theorem prime_nineteenQ_25373 : Nat.Prime 25373 := by norm_num
private theorem prime_nineteenQ_25841 : Nat.Prime 25841 := by norm_num
private theorem prime_nineteenQ_25847 : Nat.Prime 25847 := by norm_num
private theorem prime_nineteenQ_27631 : Nat.Prime 27631 := by norm_num
private theorem prime_nineteenQ_28097 : Nat.Prime 28097 := by norm_num
private theorem prime_nineteenQ_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_nineteenQ_29363 : Nat.Prime 29363 := by norm_num
private theorem prime_nineteenQ_30319 : Nat.Prime 30319 := by norm_num
private theorem prime_nineteenQ_30637 : Nat.Prime 30637 := by norm_num
private theorem prime_nineteenQ_31387 : Nat.Prime 31387 := by norm_num
private theorem prime_nineteenQ_32573 : Nat.Prime 32573 := by norm_num
private theorem prime_nineteenQ_33359 : Nat.Prime 33359 := by norm_num
private theorem prime_nineteenQ_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_nineteenQ_36497 : Nat.Prime 36497 := by norm_num
private theorem prime_nineteenQ_36551 : Nat.Prime 36551 := by norm_num
private theorem prime_nineteenQ_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_nineteenQ_38873 : Nat.Prime 38873 := by norm_num
private theorem prime_nineteenQ_39521 : Nat.Prime 39521 := by norm_num
private theorem prime_nineteenQ_40099 : Nat.Prime 40099 := by norm_num
private theorem prime_nineteenQ_42641 : Nat.Prime 42641 := by norm_num
private theorem prime_nineteenQ_44587 : Nat.Prime 44587 := by norm_num
private theorem prime_nineteenQ_51349 : Nat.Prime 51349 := by norm_num
private theorem prime_nineteenQ_51481 : Nat.Prime 51481 := by norm_num
private theorem prime_nineteenQ_54413 : Nat.Prime 54413 := by norm_num
private theorem prime_nineteenQ_54877 : Nat.Prime 54877 := by norm_num
private theorem prime_nineteenQ_55817 : Nat.Prime 55817 := by norm_num
private theorem prime_nineteenQ_56633 : Nat.Prime 56633 := by norm_num
private theorem prime_nineteenQ_57493 : Nat.Prime 57493 := by norm_num
private theorem prime_nineteenQ_59629 : Nat.Prime 59629 := by norm_num
private theorem prime_nineteenQ_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_nineteenQ_63197 : Nat.Prime 63197 := by norm_num
private theorem prime_nineteenQ_64171 : Nat.Prime 64171 := by norm_num
private theorem prime_nineteenQ_65419 : Nat.Prime 65419 := by norm_num
private theorem prime_nineteenQ_65963 : Nat.Prime 65963 := by norm_num
private theorem prime_nineteenQ_66587 : Nat.Prime 66587 := by norm_num
private theorem prime_nineteenQ_68059 : Nat.Prime 68059 := by norm_num
private theorem prime_nineteenQ_68483 : Nat.Prime 68483 := by norm_num
private theorem prime_nineteenQ_70379 : Nat.Prime 70379 := by norm_num
private theorem prime_nineteenQ_71263 : Nat.Prime 71263 := by norm_num
private theorem prime_nineteenQ_72533 : Nat.Prime 72533 := by norm_num
private theorem prime_nineteenQ_77587 : Nat.Prime 77587 := by norm_num
private theorem prime_nineteenQ_77929 : Nat.Prime 77929 := by norm_num
private theorem prime_nineteenQ_85903 : Nat.Prime 85903 := by norm_num
private theorem prime_nineteenQ_86183 : Nat.Prime 86183 := by norm_num
private theorem prime_nineteenQ_87509 : Nat.Prime 87509 := by norm_num
private theorem prime_nineteenQ_91199 : Nat.Prime 91199 := by norm_num
private theorem prime_nineteenQ_93979 : Nat.Prime 93979 := by norm_num
private theorem prime_nineteenQ_101383 : Nat.Prime 101383 := by norm_num
private theorem prime_nineteenQ_102673 : Nat.Prime 102673 := by norm_num
private theorem prime_nineteenQ_104323 : Nat.Prime 104323 := by norm_num
private theorem prime_nineteenQ_110273 : Nat.Prime 110273 := by norm_num
private theorem prime_nineteenQ_113731 : Nat.Prime 113731 := by norm_num
private theorem prime_nineteenQ_114941 : Nat.Prime 114941 := by norm_num
private theorem prime_nineteenQ_124703 : Nat.Prime 124703 := by norm_num
private theorem prime_nineteenQ_126613 : Nat.Prime 126613 := by norm_num
private theorem prime_nineteenQ_131203 : Nat.Prime 131203 := by norm_num
private theorem prime_nineteenQ_133499 : Nat.Prime 133499 := by norm_num
private theorem prime_nineteenQ_133723 : Nat.Prime 133723 := by norm_num
private theorem prime_nineteenQ_133781 : Nat.Prime 133781 := by norm_num
private theorem prime_nineteenQ_139939 : Nat.Prime 139939 := by norm_num
private theorem prime_nineteenQ_175727 : Nat.Prime 175727 := by norm_num
private theorem prime_nineteenQ_182131 : Nat.Prime 182131 := by norm_num
private theorem prime_nineteenQ_185233 : Nat.Prime 185233 := by norm_num
private theorem prime_nineteenQ_195977 : Nat.Prime 195977 := by norm_num
private theorem prime_nineteenQ_198769 : Nat.Prime 198769 := by norm_num
private theorem prime_nineteenQ_200867 : Nat.Prime 200867 := by norm_num
private theorem prime_nineteenQ_206299 : Nat.Prime 206299 := by norm_num
private theorem prime_nineteenQ_210499 : Nat.Prime 210499 := by norm_num
private theorem prime_nineteenQ_217409 : Nat.Prime 217409 := by norm_num
private theorem prime_nineteenQ_225529 : Nat.Prime 225529 := by norm_num
private theorem prime_nineteenQ_227663 : Nat.Prime 227663 := by norm_num
private theorem prime_nineteenQ_242009 : Nat.Prime 242009 := by norm_num
private theorem prime_nineteenQ_248033 : Nat.Prime 248033 := by norm_num
private theorem prime_nineteenQ_252253 : Nat.Prime 252253 := by norm_num
private theorem prime_nineteenQ_273641 : Nat.Prime 273641 := by norm_num
private theorem prime_nineteenQ_286103 : Nat.Prime 286103 := by norm_num
private theorem prime_nineteenQ_296473 : Nat.Prime 296473 := by norm_num
private theorem prime_nineteenQ_306533 : Nat.Prime 306533 := by norm_num
private theorem prime_nineteenQ_328667 : Nat.Prime 328667 := by norm_num
private theorem prime_nineteenQ_338263 : Nat.Prime 338263 := by norm_num
private theorem prime_nineteenQ_345143 : Nat.Prime 345143 := by norm_num
private theorem prime_nineteenQ_347071 : Nat.Prime 347071 := by norm_num
private theorem prime_nineteenQ_354469 : Nat.Prime 354469 := by norm_num
private theorem prime_nineteenQ_368609 : Nat.Prime 368609 := by norm_num
private theorem prime_nineteenQ_390581 : Nat.Prime 390581 := by norm_num
private theorem prime_nineteenQ_402221 : Nat.Prime 402221 := by norm_num
private theorem prime_nineteenQ_405221 : Nat.Prime 405221 := by norm_num
private theorem prime_nineteenQ_444649 : Nat.Prime 444649 := by norm_num
private theorem prime_nineteenQ_448013 : Nat.Prime 448013 := by norm_num
private theorem prime_nineteenQ_468157 : Nat.Prime 468157 := by norm_num
private theorem prime_nineteenQ_477221 : Nat.Prime 477221 := by norm_num
private theorem prime_nineteenQ_506381 : Nat.Prime 506381 := by norm_num
private theorem prime_nineteenQ_507641 : Nat.Prime 507641 := by norm_num
private theorem prime_nineteenQ_534407 : Nat.Prime 534407 := by norm_num
private theorem prime_nineteenQ_560929 : Nat.Prime 560929 := by norm_num
private theorem prime_nineteenQ_561553 : Nat.Prime 561553 := by norm_num
private theorem prime_nineteenQ_566233 : Nat.Prime 566233 := by norm_num
private theorem prime_nineteenQ_587527 : Nat.Prime 587527 := by norm_num
private theorem prime_nineteenQ_620111 : Nat.Prime 620111 := by norm_num
private theorem prime_nineteenQ_622067 : Nat.Prime 622067 := by norm_num
private theorem prime_nineteenQ_628561 : Nat.Prime 628561 := by norm_num
private theorem prime_nineteenQ_636149 : Nat.Prime 636149 := by norm_num
private theorem prime_nineteenQ_642359 : Nat.Prime 642359 := by norm_num
private theorem prime_nineteenQ_646291 : Nat.Prime 646291 := by norm_num
private theorem prime_nineteenQ_660817 : Nat.Prime 660817 := by norm_num
private theorem prime_nineteenQ_790613 : Nat.Prime 790613 := by norm_num
private theorem prime_nineteenQ_826831 : Nat.Prime 826831 := by norm_num
private theorem prime_nineteenQ_828743 : Nat.Prime 828743 := by norm_num
private theorem prime_nineteenQ_847279 : Nat.Prime 847279 := by norm_num
private theorem prime_nineteenQ_1011079 : Nat.Prime 1011079 := by norm_num
private theorem prime_nineteenQ_1042523 : Nat.Prime 1042523 := by norm_num
private theorem prime_nineteenQ_1149233 : Nat.Prime 1149233 := by norm_num
private theorem prime_nineteenQ_1183003 : Nat.Prime 1183003 := by norm_num
private theorem prime_nineteenQ_1227929 : Nat.Prime 1227929 := by norm_num
private theorem prime_nineteenQ_1239523 : Nat.Prime 1239523 := by norm_num
private theorem prime_nineteenQ_1315597 : Nat.Prime 1315597 := by norm_num
private theorem prime_nineteenQ_1318411 : Nat.Prime 1318411 := by norm_num
private theorem prime_nineteenQ_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_nineteenQ_1425953 : Nat.Prime 1425953 := by norm_num
private theorem prime_nineteenQ_1535629 : Nat.Prime 1535629 := by norm_num
private theorem prime_nineteenQ_1668889 : Nat.Prime 1668889 := by norm_num
private theorem prime_nineteenQ_1689067 : Nat.Prime 1689067 := by norm_num
private theorem prime_nineteenQ_1725697 : Nat.Prime 1725697 := by norm_num
private theorem prime_nineteenQ_1840117 : Nat.Prime 1840117 := by norm_num
private theorem prime_nineteenQ_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_nineteenQ_1917341 : Nat.Prime 1917341 := by norm_num
private theorem prime_nineteenQ_1954237 : Nat.Prime 1954237 := by norm_num
private theorem prime_nineteenQ_1961107 : Nat.Prime 1961107 := by norm_num
private theorem prime_nineteenQ_1962997 : Nat.Prime 1962997 := by norm_num
private theorem prime_nineteenQ_2093813 : Nat.Prime 2093813 := by norm_num
private theorem prime_nineteenQ_2158727 : Nat.Prime 2158727 := by norm_num
private theorem prime_nineteenQ_2212631 : Nat.Prime 2212631 := by norm_num
private theorem prime_nineteenQ_2217557 : Nat.Prime 2217557 := by norm_num
private theorem prime_nineteenQ_2261503 : Nat.Prime 2261503 := by norm_num
private theorem prime_nineteenQ_2392267 : Nat.Prime 2392267 := by norm_num
private theorem prime_nineteenQ_2629001 : Nat.Prime 2629001 := by norm_num
private theorem prime_nineteenQ_2685967 : Nat.Prime 2685967 := by norm_num
private theorem prime_nineteenQ_2691067 : Nat.Prime 2691067 := by norm_num
private theorem prime_nineteenQ_2848777 : Nat.Prime 2848777 := by norm_num
private theorem prime_nineteenQ_2912891 : Nat.Prime 2912891 := by norm_num
private theorem prime_nineteenQ_3009659 : Nat.Prime 3009659 := by norm_num
private theorem prime_nineteenQ_3014237 : Nat.Prime 3014237 := by norm_num
private theorem prime_nineteenQ_3199561 : Nat.Prime 3199561 := by norm_num
private theorem prime_nineteenQ_3714331 : Nat.Prime 3714331 := by norm_num
private theorem prime_nineteenQ_3763339 : Nat.Prime 3763339 := by norm_num
private theorem prime_nineteenQ_4014937 : Nat.Prime 4014937 := by norm_num
private theorem prime_nineteenQ_4145299 : Nat.Prime 4145299 := by norm_num
private theorem prime_nineteenQ_4624393 : Nat.Prime 4624393 := by norm_num
private theorem prime_nineteenQ_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_nineteenQ_5387951 : Nat.Prime 5387951 := by norm_num
private theorem prime_nineteenQ_5531677 : Nat.Prime 5531677 := by norm_num
private theorem prime_nineteenQ_5612447 : Nat.Prime 5612447 := by norm_num
private theorem prime_nineteenQ_5740507 : Nat.Prime 5740507 := by norm_num
private theorem prime_nineteenQ_5924683 : Nat.Prime 5924683 := by norm_num
private theorem prime_nineteenQ_6465853 : Nat.Prime 6465853 := by norm_num
private theorem prime_nineteenQ_7006843 : Nat.Prime 7006843 := by norm_num
private theorem prime_nineteenQ_7032919 : Nat.Prime 7032919 := by norm_num
private theorem prime_nineteenQ_7125277 : Nat.Prime 7125277 := by norm_num
private theorem prime_nineteenQ_7135949 : Nat.Prime 7135949 := by norm_num
private theorem prime_nineteenQ_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_nineteenQ_7439681 : Nat.Prime 7439681 := by norm_num
private theorem prime_nineteenQ_7863253 : Nat.Prime 7863253 := by norm_num
private theorem prime_nineteenQ_7910153 : Nat.Prime 7910153 := by norm_num
private theorem prime_nineteenQ_8840341 : Nat.Prime 8840341 := by norm_num
private theorem prime_nineteenQ_9415687 : Nat.Prime 9415687 := by norm_num
private theorem prime_nineteenQ_9718361 : Nat.Prime 9718361 := by norm_num
private theorem prime_nineteenQ_10394107 : Nat.Prime 10394107 := by norm_num
private theorem prime_nineteenQ_10698629 : Nat.Prime 10698629 := by norm_num
private theorem prime_nineteenQ_10747189 : Nat.Prime 10747189 := by norm_num
private theorem prime_nineteenQ_11416631 : Nat.Prime 11416631 := by norm_num
private theorem prime_nineteenQ_11704607 : Nat.Prime 11704607 := by norm_num
private theorem prime_nineteenQ_11937227 : Nat.Prime 11937227 := by norm_num
private theorem prime_nineteenQ_13250177 : Nat.Prime 13250177 := by norm_num
private theorem prime_nineteenQ_13685389 : Nat.Prime 13685389 := by norm_num
private theorem prime_nineteenQ_14238023 : Nat.Prime 14238023 := by norm_num
private theorem prime_nineteenQ_14408221 : Nat.Prime 14408221 := by norm_num
private theorem prime_nineteenQ_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_nineteenQ_19015481 : Nat.Prime 19015481 := by norm_num
private theorem prime_nineteenQ_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_nineteenQ_22638193 : Nat.Prime 22638193 := by norm_num
private theorem prime_nineteenQ_24337051 : Nat.Prime 24337051 := by norm_num
private theorem prime_nineteenQ_26713663 : Nat.Prime 26713663 := by norm_num

private theorem prime_nineteenQ_32628257 : Nat.Prime 32628257 := by
  apply lucas_primality 32628257 (3 : ZMod 32628257)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (859, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (859, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) = 32628257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_859
      · exact prime_nineteenQ_1187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32628257) ^ 16314128 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 32628257) ^ 37984 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 32628257) ^ 27488 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_38925583 : Nat.Prime 38925583 := by
  apply lucas_primality 38925583 (3 : ZMod 38925583)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (251, 1), (25847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (251, 1), (25847, 1)] : List FactorBlock).map factorBlockValue).prod) = 38925583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_251
      · exact prime_nineteenQ_25847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38925583) ^ 19462791 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38925583) ^ 12975194 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38925583) ^ 155082 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38925583) ^ 1506 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_39314563 : Nat.Prime 39314563 := by
  apply lucas_primality 39314563 (3 : ZMod 39314563)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (133723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (133723, 1)] : List FactorBlock).map factorBlockValue).prod) = 39314563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_133723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39314563) ^ 19657281 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39314563) ^ 13104854 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39314563) ^ 5616366 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39314563) ^ 294 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_42041059 : Nat.Prime 42041059 := by
  apply lucas_primality 42041059 (2 : ZMod 42041059)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7006843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7006843, 1)] : List FactorBlock).map factorBlockValue).prod) = 42041059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7006843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42041059) ^ 21020529 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42041059) ^ 14013686 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42041059) ^ 6 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_43086893 : Nat.Prime 43086893 := by
  apply lucas_primality 43086893 (2 : ZMod 43086893)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (601, 1), (17923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (601, 1), (17923, 1)] : List FactorBlock).map factorBlockValue).prod) = 43086893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_601
      · exact prime_nineteenQ_17923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43086893) ^ 21543446 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43086893) ^ 71692 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43086893) ^ 2404 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_49146259 : Nat.Prime 49146259 := by
  apply lucas_primality 49146259 (7 : ZMod 49146259)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (409, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (409, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 49146259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_409
      · exact prime_nineteenQ_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 49146259) ^ 24573129 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 16382086 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 7020894 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 120162 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49146259) ^ 17178 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_52362491 : Nat.Prime 52362491 := by
  apply lucas_primality 52362491 (2 : ZMod 52362491)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (227663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (227663, 1)] : List FactorBlock).map factorBlockValue).prod) = 52362491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_227663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52362491) ^ 26181245 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52362491) ^ 10472498 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52362491) ^ 2276630 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52362491) ^ 230 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_53042047 : Nat.Prime 53042047 := by
  apply lucas_primality 53042047 (6 : ZMod 53042047)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8840341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8840341, 1)] : List FactorBlock).map factorBlockValue).prod) = 53042047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_8840341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 53042047) ^ 26521023 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 53042047) ^ 17680682 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 53042047) ^ 6 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_53225903 : Nat.Prime 53225903 := by
  apply lucas_primality 53225903 (5 : ZMod 53225903)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (566233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (566233, 1)] : List FactorBlock).map factorBlockValue).prod) = 53225903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_566233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 53225903) ^ 26612951 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 53225903) ^ 1132466 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 53225903) ^ 94 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_58627111 : Nat.Prime 58627111 := by
  apply lucas_primality 58627111 (3 : ZMod 58627111)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1954237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1954237, 1)] : List FactorBlock).map factorBlockValue).prod) = 58627111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_1954237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58627111) ^ 29313555 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58627111) ^ 19542370 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58627111) ^ 11725422 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58627111) ^ 30 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_59767193 : Nat.Prime 59767193 := by
  apply lucas_primality 59767193 (3 : ZMod 59767193)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (72533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (72533, 1)] : List FactorBlock).map factorBlockValue).prod) = 59767193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_103
      · exact prime_nineteenQ_72533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59767193) ^ 29883596 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 59767193) ^ 580264 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 59767193) ^ 824 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_65699149 : Nat.Prime 65699149 := by
  apply lucas_primality 65699149 (2 : ZMod 65699149)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (65963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (65963, 1)] : List FactorBlock).map factorBlockValue).prod) = 65699149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_83
      · exact prime_nineteenQ_65963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65699149) ^ 32849574 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 65699149) ^ 21899716 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 65699149) ^ 791556 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 65699149) ^ 996 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_78438047 : Nat.Prime 78438047 := by
  apply lucas_primality 78438047 (5 : ZMod 78438047)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (347071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (347071, 1)] : List FactorBlock).map factorBlockValue).prod) = 78438047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_113
      · exact prime_nineteenQ_347071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 78438047) ^ 39219023 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 78438047) ^ 694142 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 78438047) ^ 226 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_79559329 : Nat.Prime 79559329 := by
  apply lucas_primality 79559329 (7 : ZMod 79559329)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (828743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (828743, 1)] : List FactorBlock).map factorBlockValue).prod) = 79559329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_828743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 79559329) ^ 39779664 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 79559329) ^ 26519776 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 79559329) ^ 96 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_82208521 : Nat.Prime 82208521 := by
  apply lucas_primality 82208521 (7 : ZMod 82208521)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) = 82208521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_25373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 82208521) ^ 41104260 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82208521) ^ 27402840 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82208521) ^ 16441704 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82208521) ^ 3240 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_85171937 : Nat.Prime 85171937 := by
  apply lucas_primality 85171937 (3 : ZMod 85171937)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (103, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (103, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) = 85171937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_103
      · exact prime_nineteenQ_25841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 85171937) ^ 42585968 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 85171937) ^ 826912 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 85171937) ^ 3296 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_91582019 : Nat.Prime 91582019 := by
  apply lucas_primality 91582019 (2 : ZMod 91582019)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (109, 1), (181, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (109, 1), (181, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 91582019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_109
      · exact prime_nineteenQ_181
      · exact prime_nineteenQ_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91582019) ^ 45791009 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91582019) ^ 8325638 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91582019) ^ 840202 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91582019) ^ 505978 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91582019) ^ 434038 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_94644037 : Nat.Prime 94644037 := by
  apply lucas_primality 94644037 (2 : ZMod 94644037)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2629001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2629001, 1)] : List FactorBlock).map factorBlockValue).prod) = 94644037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_2629001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94644037) ^ 47322018 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94644037) ^ 31548012 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94644037) ^ 36 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_110631551 : Nat.Prime 110631551 := by
  apply lucas_primality 110631551 (7 : ZMod 110631551)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2212631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2212631, 1)] : List FactorBlock).map factorBlockValue).prod) = 110631551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_2212631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 110631551) ^ 55315775 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 110631551) ^ 22126310 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 110631551) ^ 50 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_111343009 : Nat.Prime 111343009 := by
  apply lucas_primality 111343009 (11 : ZMod 111343009)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (223, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (223, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) = 111343009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_223
      · exact prime_nineteenQ_743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 111343009) ^ 55671504 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 111343009) ^ 37114336 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 111343009) ^ 15906144 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 111343009) ^ 499296 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 111343009) ^ 149856 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_112624157 : Nat.Prime 112624157 := by
  apply lucas_primality 112624157 (2 : ZMod 112624157)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (477221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (477221, 1)] : List FactorBlock).map factorBlockValue).prod) = 112624157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_477221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 112624157) ^ 56312078 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 112624157) ^ 1908884 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 112624157) ^ 236 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_128926417 : Nat.Prime 128926417 := by
  apply lucas_primality 128926417 (5 : ZMod 128926417)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2685967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2685967, 1)] : List FactorBlock).map factorBlockValue).prod) = 128926417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_2685967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 128926417) ^ 64463208 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 128926417) ^ 42975472 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 128926417) ^ 48 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_129713707 : Nat.Prime 129713707 := by
  apply lucas_primality 129713707 (5 : ZMod 129713707)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (109, 1), (3889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (109, 1), (3889, 1)] : List FactorBlock).map factorBlockValue).prod) = 129713707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_109
      · exact prime_nineteenQ_3889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 129713707) ^ 64856853 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 43237902 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 7630218 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 1190034 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129713707) ^ 33354 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_148153039 : Nat.Prime 148153039 := by
  apply lucas_primality 148153039 (6 : ZMod 148153039)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (347, 1), (6469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (347, 1), (6469, 1)] : List FactorBlock).map factorBlockValue).prod) = 148153039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_347
      · exact prime_nineteenQ_6469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 148153039) ^ 74076519 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 148153039) ^ 49384346 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 148153039) ^ 13468458 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 148153039) ^ 426954 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 148153039) ^ 22902 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_153387281 : Nat.Prime 153387281 := by
  apply lucas_primality 153387281 (3 : ZMod 153387281)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1917341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1917341, 1)] : List FactorBlock).map factorBlockValue).prod) = 153387281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_1917341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 153387281) ^ 76693640 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 153387281) ^ 30677456 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 153387281) ^ 80 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_155702333 : Nat.Prime 155702333 := by
  apply lucas_primality 155702333 (2 : ZMod 155702333)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (38925583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (38925583, 1)] : List FactorBlock).map factorBlockValue).prod) = 155702333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_38925583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 155702333) ^ 77851166 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 155702333) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_158598107 : Nat.Prime 158598107 := by
  apply lucas_primality 158598107 (2 : ZMod 158598107)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5261, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5261, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) = 158598107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5261
      · exact prime_nineteenQ_15073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158598107) ^ 79299053 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 158598107) ^ 30146 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 158598107) ^ 10522 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_218059319 : Nat.Prime 218059319 := by
  apply lucas_primality 218059319 (7 : ZMod 218059319)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (1535629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (1535629, 1)] : List FactorBlock).map factorBlockValue).prod) = 218059319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_71
      · exact prime_nineteenQ_1535629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 218059319) ^ 109029659 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 218059319) ^ 3071258 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 218059319) ^ 142 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_227657383 : Nat.Prime 227657383 := by
  apply lucas_primality 227657383 (3 : ZMod 227657383)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (534407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (534407, 1)] : List FactorBlock).map factorBlockValue).prod) = 227657383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_71
      · exact prime_nineteenQ_534407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 227657383) ^ 113828691 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 227657383) ^ 75885794 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 227657383) ^ 3206442 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 227657383) ^ 426 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_253697251 : Nat.Prime 253697251 := by
  apply lucas_primality 253697251 (10 : ZMod 253697251)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (338263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (338263, 1)] : List FactorBlock).map factorBlockValue).prod) = 253697251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_338263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 253697251) ^ 126848625 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 253697251) ^ 84565750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 253697251) ^ 50739450 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 253697251) ^ 750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_254872777 : Nat.Prime 254872777 := by
  apply lucas_primality 254872777 (5 : ZMod 254872777)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (743, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (743, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) = 254872777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_743
      · exact prime_nineteenQ_14293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 254872777) ^ 127436388 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 254872777) ^ 84957592 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 254872777) ^ 343032 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 254872777) ^ 17832 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_264938021 : Nat.Prime 264938021 := by
  apply lucas_primality 264938021 (2 : ZMod 264938021)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (773, 1), (17137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (773, 1), (17137, 1)] : List FactorBlock).map factorBlockValue).prod) = 264938021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_773
      · exact prime_nineteenQ_17137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 264938021) ^ 132469010 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 264938021) ^ 52987604 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 264938021) ^ 342740 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 264938021) ^ 15460 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_267425593 : Nat.Prime 267425593 := by
  apply lucas_primality 267425593 (5 : ZMod 267425593)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (31, 1), (51349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (31, 1), (51349, 1)] : List FactorBlock).map factorBlockValue).prod) = 267425593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_51349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 267425593) ^ 133712796 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 267425593) ^ 89141864 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 267425593) ^ 38203656 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 267425593) ^ 8626632 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 267425593) ^ 5208 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_282797033 : Nat.Prime 282797033 := by
  apply lucas_primality 282797033 (3 : ZMod 282797033)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (757, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (757, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 282797033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_757
      · exact prime_nineteenQ_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 282797033) ^ 141398516 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 282797033) ^ 40399576 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 282797033) ^ 373576 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 282797033) ^ 296744 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_329039453 : Nat.Prime 329039453 := by
  apply lucas_primality 329039453 (2 : ZMod 329039453)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (405221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (405221, 1)] : List FactorBlock).map factorBlockValue).prod) = 329039453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_405221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 329039453) ^ 164519726 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 329039453) ^ 47005636 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 329039453) ^ 11346188 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 329039453) ^ 812 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_359419759 : Nat.Prime 359419759 := by
  apply lucas_primality 359419759 (6 : ZMod 359419759)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (67, 1), (38873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (67, 1), (38873, 1)] : List FactorBlock).map factorBlockValue).prod) = 359419759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_38873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 359419759) ^ 179709879 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 119806586 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 15626946 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 5364474 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 359419759) ^ 9246 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_387951181 : Nat.Prime 387951181 := by
  apply lucas_primality 387951181 (17 : ZMod 387951181)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6465853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6465853, 1)] : List FactorBlock).map factorBlockValue).prod) = 387951181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_6465853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 387951181) ^ 193975590 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 387951181) ^ 129317060 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 387951181) ^ 77590236 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 387951181) ^ 60 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_400897579 : Nat.Prime 400897579 := by
  apply lucas_primality 400897579 (2 : ZMod 400897579)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3643, 1), (18341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3643, 1), (18341, 1)] : List FactorBlock).map factorBlockValue).prod) = 400897579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_3643
      · exact prime_nineteenQ_18341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 400897579) ^ 200448789 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 400897579) ^ 133632526 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 400897579) ^ 110046 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 400897579) ^ 21858 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_454695737 : Nat.Prime 454695737 := by
  apply lucas_primality 454695737 (3 : ZMod 454695737)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (17, 1), (27631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (17, 1), (27631, 1)] : List FactorBlock).map factorBlockValue).prod) = 454695737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_27631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 454695737) ^ 227347868 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 454695737) ^ 41335976 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 454695737) ^ 26746808 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 454695737) ^ 16456 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_515705669 : Nat.Prime 515705669 := by
  apply lucas_primality 515705669 (2 : ZMod 515705669)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (128926417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (128926417, 1)] : List FactorBlock).map factorBlockValue).prod) = 515705669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_128926417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 515705669) ^ 257852834 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 515705669) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_547396931 : Nat.Prime 547396931 := by
  apply lucas_primality 547396931 (2 : ZMod 547396931)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6719, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6719, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) = 547396931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_6719
      · exact prime_nineteenQ_8147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 547396931) ^ 273698465 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 547396931) ^ 109479386 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 547396931) ^ 81470 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 547396931) ^ 67190 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_619561331 : Nat.Prime 619561331 := by
  apply lucas_primality 619561331 (2 : ZMod 619561331)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1129, 1), (54877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1129, 1), (54877, 1)] : List FactorBlock).map factorBlockValue).prod) = 619561331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_1129
      · exact prime_nineteenQ_54877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 619561331) ^ 309780665 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 619561331) ^ 123912266 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 619561331) ^ 548770 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 619561331) ^ 11290 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_624954791 : Nat.Prime 624954791 := by
  apply lucas_primality 624954791 (26 : ZMod 624954791)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (1689067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (1689067, 1)] : List FactorBlock).map factorBlockValue).prod) = 624954791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_1689067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 624954791) ^ 312477395 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (26 : ZMod 624954791) ^ 124990958 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (26 : ZMod 624954791) ^ 16890670 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (26 : ZMod 624954791) ^ 370 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_663789307 : Nat.Prime 663789307 := by
  apply lucas_primality 663789307 (3 : ZMod 663789307)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (110631551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (110631551, 1)] : List FactorBlock).map factorBlockValue).prod) = 663789307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_110631551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 663789307) ^ 331894653 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 663789307) ^ 221263102 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 663789307) ^ 6 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_691107271 : Nat.Prime 691107271 := by
  apply lucas_primality 691107271 (6 : ZMod 691107271)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 3), (47, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 3), (47, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod) = 691107271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_1429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 691107271) ^ 345553635 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 691107271) ^ 230369090 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 691107271) ^ 138221454 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 691107271) ^ 98729610 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 691107271) ^ 14704410 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 691107271) ^ 483630 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_791502073 : Nat.Prime 791502073 := by
  apply lucas_primality 791502073 (5 : ZMod 791502073)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4969, 1), (6637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4969, 1), (6637, 1)] : List FactorBlock).map factorBlockValue).prod) = 791502073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_4969
      · exact prime_nineteenQ_6637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 791502073) ^ 395751036 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 791502073) ^ 263834024 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 791502073) ^ 159288 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 791502073) ^ 119256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_845348629 : Nat.Prime 845348629 := by
  apply lucas_primality 845348629 (2 : ZMod 845348629)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (646291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (646291, 1)] : List FactorBlock).map factorBlockValue).prod) = 845348629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_109
      · exact prime_nineteenQ_646291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 845348629) ^ 422674314 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 845348629) ^ 281782876 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 845348629) ^ 7755492 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 845348629) ^ 1308 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1189299689 : Nat.Prime 1189299689 := by
  apply lucas_primality 1189299689 (3 : ZMod 1189299689)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (113, 1), (1315597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (113, 1), (1315597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1189299689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_113
      · exact prime_nineteenQ_1315597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1189299689) ^ 594649844 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189299689) ^ 10524776 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189299689) ^ 904 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_113
      · exact prime_nineteenQ_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1337232557 : Nat.Prime 1337232557 := by
  apply lucas_primality 1337232557 (2 : ZMod 1337232557)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (769, 1), (39521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (769, 1), (39521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1337232557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_769
      · exact prime_nineteenQ_39521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1337232557) ^ 668616278 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337232557) ^ 121566596 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337232557) ^ 1738924 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337232557) ^ 33836 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1631881507 : Nat.Prime 1631881507 := by
  apply lucas_primality 1631881507 (5 : ZMod 1631881507)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (269, 1), (1011079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (269, 1), (1011079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631881507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_269
      · exact prime_nineteenQ_1011079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1631881507) ^ 815940753 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1631881507) ^ 543960502 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1631881507) ^ 6066474 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1631881507) ^ 1614 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1641559109 : Nat.Prime 1641559109 := by
  apply lucas_primality 1641559109 (2 : ZMod 1641559109)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (58627111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (58627111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1641559109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_58627111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1641559109) ^ 820779554 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1641559109) ^ 234508444 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1641559109) ^ 28 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1655067107 : Nat.Prime 1655067107 := by
  apply lucas_primality 1655067107 (2 : ZMod 1655067107)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (10747189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (10747189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1655067107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_10747189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1655067107) ^ 827533553 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1655067107) ^ 236438158 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1655067107) ^ 150460646 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1655067107) ^ 154 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2197968457 : Nat.Prime 2197968457 := by
  apply lucas_primality 2197968457 (7 : ZMod 2197968457)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (91582019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (91582019, 1)] : List FactorBlock).map factorBlockValue).prod) = 2197968457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_91582019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2197968457) ^ 1098984228 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2197968457) ^ 732656152 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2197968457) ^ 24 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2754168409 : Nat.Prime 2754168409 := by
  apply lucas_primality 2754168409 (7 : ZMod 2754168409)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (37, 1), (54413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (37, 1), (54413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754168409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_54413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2754168409) ^ 1377084204 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 918056136 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 144956232 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 74436984 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2754168409) ^ 50616 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2860475747 : Nat.Prime 2860475747 := by
  apply lucas_primality 2860475747 (2 : ZMod 2860475747)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (857, 1), (1668889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (857, 1), (1668889, 1)] : List FactorBlock).map factorBlockValue).prod) = 2860475747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_857
      · exact prime_nineteenQ_1668889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2860475747) ^ 1430237873 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860475747) ^ 3337778 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860475747) ^ 1714 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_3054186173 : Nat.Prime 3054186173 := by
  apply lucas_primality 3054186173 (2 : ZMod 3054186173)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (7135949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (7135949, 1)] : List FactorBlock).map factorBlockValue).prod) = 3054186173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_107
      · exact prime_nineteenQ_7135949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3054186173) ^ 1527093086 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3054186173) ^ 28543796 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3054186173) ^ 428 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_4059893807 : Nat.Prime 4059893807 := by
  apply lucas_primality 4059893807 (5 : ZMod 4059893807)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (197, 1), (448013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (197, 1), (448013, 1)] : List FactorBlock).map factorBlockValue).prod) = 4059893807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_197
      · exact prime_nineteenQ_448013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4059893807) ^ 2029946903 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4059893807) ^ 176517122 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4059893807) ^ 20608598 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4059893807) ^ 9062 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_4536589979 : Nat.Prime 4536589979 := by
  apply lucas_primality 4536589979 (2 : ZMod 4536589979)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1279, 1), (104323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1279, 1), (104323, 1)] : List FactorBlock).map factorBlockValue).prod) = 4536589979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_1279
      · exact prime_nineteenQ_104323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4536589979) ^ 2268294989 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4536589979) ^ 266858234 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4536589979) ^ 3546982 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4536589979) ^ 43486 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_5599231751 : Nat.Prime 5599231751 := by
  apply lucas_primality 5599231751 (7 : ZMod 5599231751)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (3199561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (3199561, 1)] : List FactorBlock).map factorBlockValue).prod) = 5599231751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_3199561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5599231751) ^ 2799615875 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5599231751) ^ 1119846350 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5599231751) ^ 799890250 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5599231751) ^ 1750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_6312998353 : Nat.Prime 6312998353 := by
  apply lucas_primality 6312998353 (5 : ZMod 6312998353)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (1962997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (1962997, 1)] : List FactorBlock).map factorBlockValue).prod) = 6312998353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_1962997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6312998353) ^ 3156499176 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6312998353) ^ 2104332784 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6312998353) ^ 94223856 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6312998353) ^ 3216 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_6441014959 : Nat.Prime 6441014959 := by
  apply lucas_primality 6441014959 (3 : ZMod 6441014959)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (181, 1), (847279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (181, 1), (847279, 1)] : List FactorBlock).map factorBlockValue).prod) = 6441014959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_181
      · exact prime_nineteenQ_847279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6441014959) ^ 3220507479 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6441014959) ^ 2147004986 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6441014959) ^ 920144994 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6441014959) ^ 35585718 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6441014959) ^ 7602 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_7016656643 : Nat.Prime 7016656643 := by
  apply lucas_primality 7016656643 (2 : ZMod 7016656643)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (9718361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (9718361, 1)] : List FactorBlock).map factorBlockValue).prod) = 7016656643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_9718361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7016656643) ^ 3508328321 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7016656643) ^ 369297718 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7016656643) ^ 722 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_7524292513 : Nat.Prime 7524292513 := by
  apply lucas_primality 7524292513 (5 : ZMod 7524292513)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (7125277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (7125277, 1)] : List FactorBlock).map factorBlockValue).prod) = 7524292513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_7125277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7524292513) ^ 3762146256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524292513) ^ 2508097504 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524292513) ^ 684026592 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524292513) ^ 1056 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_7669364051 : Nat.Prime 7669364051 := by
  apply lucas_primality 7669364051 (2 : ZMod 7669364051)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (153387281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (153387281, 1)] : List FactorBlock).map factorBlockValue).prod) = 7669364051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_153387281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7669364051) ^ 3834682025 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7669364051) ^ 1533872810 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7669364051) ^ 50 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_7899779621 : Nat.Prime 7899779621 := by
  apply lucas_primality 7899779621 (2 : ZMod 7899779621)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (277, 1), (1425953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (277, 1), (1425953, 1)] : List FactorBlock).map factorBlockValue).prod) = 7899779621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_277
      · exact prime_nineteenQ_1425953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7899779621) ^ 3949889810 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7899779621) ^ 1579955924 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7899779621) ^ 28519060 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7899779621) ^ 5540 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_8599279487 : Nat.Prime 8599279487 := by
  apply lucas_primality 8599279487 (5 : ZMod 8599279487)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (107, 1), (5740507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (107, 1), (5740507, 1)] : List FactorBlock).map factorBlockValue).prod) = 8599279487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_107
      · exact prime_nineteenQ_5740507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8599279487) ^ 4299639743 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8599279487) ^ 1228468498 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8599279487) ^ 80367098 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8599279487) ^ 1498 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_9340143089 : Nat.Prime 9340143089 := by
  apply lucas_primality 9340143089 (3 : ZMod 9340143089)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (14238023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (14238023, 1)] : List FactorBlock).map factorBlockValue).prod) = 9340143089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_14238023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9340143089) ^ 4670071544 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9340143089) ^ 227808368 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9340143089) ^ 656 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_9955301119 : Nat.Prime 9955301119 := by
  apply lucas_primality 9955301119 (15 : ZMod 9955301119)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1051, 1), (225529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1051, 1), (225529, 1)] : List FactorBlock).map factorBlockValue).prod) = 9955301119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_1051
      · exact prime_nineteenQ_225529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 9955301119) ^ 4977650559 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 3318433706 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 1422185874 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 9472218 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 9955301119) ^ 44142 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_10143596371 : Nat.Prime 10143596371 := by
  apply lucas_primality 10143596371 (2 : ZMod 10143596371)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (7863253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (7863253, 1)] : List FactorBlock).map factorBlockValue).prod) = 10143596371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_7863253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10143596371) ^ 5071798185 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 3381198790 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 2028719274 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 235897590 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143596371) ^ 1290 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_12831738653 : Nat.Prime 12831738653 := by
  apply lucas_primality 12831738653 (2 : ZMod 12831738653)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (47, 1), (4014937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (47, 1), (4014937, 1)] : List FactorBlock).map factorBlockValue).prod) = 12831738653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_4014937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12831738653) ^ 6415869326 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831738653) ^ 754808156 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831738653) ^ 273015716 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831738653) ^ 3196 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_14199409481 : Nat.Prime 14199409481 := by
  apply lucas_primality 14199409481 (3 : ZMod 14199409481)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (449, 1), (790613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (449, 1), (790613, 1)] : List FactorBlock).map factorBlockValue).prod) = 14199409481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_449
      · exact prime_nineteenQ_790613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14199409481) ^ 7099704740 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14199409481) ^ 2839881896 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14199409481) ^ 31624520 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14199409481) ^ 17960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_16627372351 : Nat.Prime 16627372351 := by
  apply lucas_primality 16627372351 (6 : ZMod 16627372351)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (397, 1), (9007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (397, 1), (9007, 1)] : List FactorBlock).map factorBlockValue).prod) = 16627372351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_397
      · exact prime_nineteenQ_9007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16627372351) ^ 8313686175 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16627372351) ^ 5542457450 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16627372351) ^ 3325474470 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16627372351) ^ 536366850 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16627372351) ^ 41882550 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16627372351) ^ 1846050 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_16925396167 : Nat.Prime 16925396167 := by
  apply lucas_primality 16925396167 (3 : ZMod 16925396167)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (73, 1), (1840117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (73, 1), (1840117, 1)] : List FactorBlock).map factorBlockValue).prod) = 16925396167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_73
      · exact prime_nineteenQ_1840117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16925396167) ^ 8462698083 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16925396167) ^ 5641798722 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16925396167) ^ 2417913738 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16925396167) ^ 231854742 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16925396167) ^ 9198 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_17369393617 : Nat.Prime 17369393617 := by
  apply lucas_primality 17369393617 (5 : ZMod 17369393617)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (367, 1), (328667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (367, 1), (328667, 1)] : List FactorBlock).map factorBlockValue).prod) = 17369393617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_367
      · exact prime_nineteenQ_328667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17369393617) ^ 8684696808 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 17369393617) ^ 5789797872 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 17369393617) ^ 47328048 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 17369393617) ^ 52848 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_17404397201 : Nat.Prime 17404397201 := by
  apply lucas_primality 17404397201 (6 : ZMod 17404397201)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (73, 1), (577, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (73, 1), (577, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 17404397201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_73
      · exact prime_nineteenQ_577
      · exact prime_nineteenQ_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17404397201) ^ 8702198600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 3480879440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 238416400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 30163600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 17404397201) ^ 16848400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_17671339223 : Nat.Prime 17671339223 := by
  apply lucas_primality 17671339223 (5 : ZMod 17671339223)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4093, 1), (2158727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4093, 1), (2158727, 1)] : List FactorBlock).map factorBlockValue).prod) = 17671339223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_4093
      · exact prime_nineteenQ_2158727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17671339223) ^ 8835669611 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 17671339223) ^ 4317454 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 17671339223) ^ 8186 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_18201107173 : Nat.Prime 18201107173 := by
  apply lucas_primality 18201107173 (2 : ZMod 18201107173)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (22638193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (22638193, 1)] : List FactorBlock).map factorBlockValue).prod) = 18201107173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_22638193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18201107173) ^ 9100553586 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18201107173) ^ 6067035724 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18201107173) ^ 271658316 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18201107173) ^ 804 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_20128140817 : Nat.Prime 20128140817 := by
  apply lucas_primality 20128140817 (5 : ZMod 20128140817)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (773, 1), (11071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (773, 1), (11071, 1)] : List FactorBlock).map factorBlockValue).prod) = 20128140817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_773
      · exact prime_nineteenQ_11071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20128140817) ^ 10064070408 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20128140817) ^ 6709380272 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20128140817) ^ 2875448688 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20128140817) ^ 26038992 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20128140817) ^ 1818096 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_21798326621 : Nat.Prime 21798326621 := by
  apply lucas_primality 21798326621 (2 : ZMod 21798326621)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (155702333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (155702333, 1)] : List FactorBlock).map factorBlockValue).prod) = 21798326621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_155702333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21798326621) ^ 10899163310 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21798326621) ^ 4359665324 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21798326621) ^ 3114046660 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21798326621) ^ 140 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_25121561411 : Nat.Prime 25121561411 := by
  apply lucas_primality 25121561411 (6 : ZMod 25121561411)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (41, 1), (506381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (41, 1), (506381, 1)] : List FactorBlock).map factorBlockValue).prod) = 25121561411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_506381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 25121561411) ^ 12560780705 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 5024312282 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 2283778310 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 612721010 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25121561411) ^ 49610 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_25340904301 : Nat.Prime 25340904301 := by
  apply lucas_primality 25340904301 (2 : ZMod 25340904301)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (83, 1), (839, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (83, 1), (839, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 25340904301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_83
      · exact prime_nineteenQ_839
      · exact prime_nineteenQ_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25340904301) ^ 12670452150 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 8446968100 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 5068180860 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 305312100 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 30203700 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25340904301) ^ 20891100 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_32318626891 : Nat.Prime 32318626891 := by
  apply lucas_primality 32318626891 (2 : ZMod 32318626891)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (29, 1), (337, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (29, 1), (337, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 32318626891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_337
      · exact prime_nineteenQ_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32318626891) ^ 16159313445 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 10772875630 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 6463725378 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 2938056990 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 1114435410 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 95900970 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32318626891) ^ 35475990 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_51862708169 : Nat.Prime 51862708169 := by
  apply lucas_primality 51862708169 (3 : ZMod 51862708169)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (443, 1), (248033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (443, 1), (248033, 1)] : List FactorBlock).map factorBlockValue).prod) = 51862708169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_443
      · exact prime_nineteenQ_248033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51862708169) ^ 25931354084 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51862708169) ^ 879028952 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51862708169) ^ 117071576 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51862708169) ^ 209096 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_52600248139 : Nat.Prime 52600248139 := by
  apply lucas_primality 52600248139 (2 : ZMod 52600248139)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (282797033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (282797033, 1)] : List FactorBlock).map factorBlockValue).prod) = 52600248139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_282797033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52600248139) ^ 26300124069 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600248139) ^ 17533416046 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600248139) ^ 1696782198 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600248139) ^ 186 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_57451848793 : Nat.Prime 57451848793 := by
  apply lucas_primality 57451848793 (5 : ZMod 57451848793)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 3), (389, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 3), (389, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) = 57451848793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_389
      · exact prime_nineteenQ_2801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57451848793) ^ 28725924396 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 19150616264 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 4419372984 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 147691128 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 57451848793) ^ 20511192 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_58384288267 : Nat.Prime 58384288267 := by
  apply lucas_primality 58384288267 (2 : ZMod 58384288267)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (373, 1), (379, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (373, 1), (379, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 58384288267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_373
      · exact prime_nineteenQ_379
      · exact prime_nineteenQ_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58384288267) ^ 29192144133 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 19461429422 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 3434369898 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 156526242 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 154048254 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58384288267) ^ 14419434 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_73373669287 : Nat.Prime 73373669287 := by
  apply lucas_primality 73373669287 (3 : ZMod 73373669287)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (2579, 1), (110273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (2579, 1), (110273, 1)] : List FactorBlock).map factorBlockValue).prod) = 73373669287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_2579
      · exact prime_nineteenQ_110273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73373669287) ^ 36686834643 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73373669287) ^ 24457889762 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73373669287) ^ 1706364402 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73373669287) ^ 28450434 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73373669287) ^ 665382 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_94167868097 : Nat.Prime 94167868097 := by
  apply lucas_primality 94167868097 (3 : ZMod 94167868097)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (1163, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (1163, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) = 94167868097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_1163
      · exact prime_nineteenQ_66587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 94167868097) ^ 47083934048 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 94167868097) ^ 4956203584 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 94167868097) ^ 80969792 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 94167868097) ^ 1414208 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_96544698707 : Nat.Prime 96544698707 := by
  apply lucas_primality 96544698707 (2 : ZMod 96544698707)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (127, 1), (3763339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (127, 1), (3763339, 1)] : List FactorBlock).map factorBlockValue).prod) = 96544698707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_101
      · exact prime_nineteenQ_127
      · exact prime_nineteenQ_3763339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96544698707) ^ 48272349353 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 96544698707) ^ 955888106 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 96544698707) ^ 760194478 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 96544698707) ^ 25654 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_103811766649 : Nat.Prime 103811766649 := by
  apply lucas_primality 103811766649 (7 : ZMod 103811766649)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (227657383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (227657383, 1)] : List FactorBlock).map factorBlockValue).prod) = 103811766649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_227657383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 103811766649) ^ 51905883324 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 103811766649) ^ 34603922216 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 103811766649) ^ 5463777192 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 103811766649) ^ 456 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_109926847451 : Nat.Prime 109926847451 := by
  apply lucas_primality 109926847451 (6 : ZMod 109926847451)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (19, 1), (23, 1), (102673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (19, 1), (23, 1), (102673, 1)] : List FactorBlock).map factorBlockValue).prod) = 109926847451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_102673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109926847451) ^ 54963423725 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 21985369490 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 15703835350 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 5785623550 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 4779428150 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 109926847451) ^ 1070650 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_112971088693 : Nat.Prime 112971088693 := by
  apply lucas_primality 112971088693 (6 : ZMod 112971088693)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (1609, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (1609, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 112971088693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_1609
      · exact prime_nineteenQ_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 112971088693) ^ 56485544346 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 37657029564 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 16138726956 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 10270098972 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 70211988 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 112971088693) ^ 13380444 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_120808277411 : Nat.Prime 120808277411 := by
  apply lucas_primality 120808277411 (6 : ZMod 120808277411)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (769, 1), (826831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (769, 1), (826831, 1)] : List FactorBlock).map factorBlockValue).prod) = 120808277411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_769
      · exact prime_nineteenQ_826831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 120808277411) ^ 60404138705 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 120808277411) ^ 24161655482 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 120808277411) ^ 6358330390 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 120808277411) ^ 157097890 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 120808277411) ^ 146110 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_138529476269 : Nat.Prime 138529476269 := by
  apply lucas_primality 138529476269 (2 : ZMod 138529476269)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 2), (2293, 1), (17959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 2), (2293, 1), (17959, 1)] : List FactorBlock).map factorBlockValue).prod) = 138529476269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_2293
      · exact prime_nineteenQ_17959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 138529476269) ^ 69264738134 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 138529476269) ^ 4776878492 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 138529476269) ^ 60414076 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 138529476269) ^ 7713652 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_147942152269 : Nat.Prime 147942152269 := by
  apply lucas_primality 147942152269 (2 : ZMod 147942152269)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (907, 1), (124703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (907, 1), (124703, 1)] : List FactorBlock).map factorBlockValue).prod) = 147942152269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_109
      · exact prime_nineteenQ_907
      · exact prime_nineteenQ_124703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147942152269) ^ 73971076134 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 147942152269) ^ 49314050756 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 147942152269) ^ 1357267452 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 147942152269) ^ 163111524 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 147942152269) ^ 1186356 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_150009781321 : Nat.Prime 150009781321 := by
  apply lucas_primality 150009781321 (34 : ZMod 150009781321)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (29, 1), (67, 1), (30637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (29, 1), (67, 1), (30637, 1)] : List FactorBlock).map factorBlockValue).prod) = 150009781321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_30637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 150009781321) ^ 75004890660 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 150009781321) ^ 50003260440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 150009781321) ^ 30001956264 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 150009781321) ^ 21429968760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 150009781321) ^ 5172751080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 150009781321) ^ 2238951960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 150009781321) ^ 4896360 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_177204535801 : Nat.Prime 177204535801 := by
  apply lucas_primality 177204535801 (11 : ZMod 177204535801)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (89, 1), (1451, 1), (2287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (89, 1), (1451, 1), (2287, 1)] : List FactorBlock).map factorBlockValue).prod) = 177204535801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_89
      · exact prime_nineteenQ_1451
      · exact prime_nineteenQ_2287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 177204535801) ^ 88602267900 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 59068178600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 35440907160 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 1991062200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 122125800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 177204535801) ^ 77483400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_177402750137 : Nat.Prime 177402750137 := by
  apply lucas_primality 177402750137 (3 : ZMod 177402750137)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (515705669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (515705669, 1)] : List FactorBlock).map factorBlockValue).prod) = 177402750137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_515705669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 177402750137) ^ 88701375068 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 177402750137) ^ 4125645352 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 177402750137) ^ 344 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_196987093081 : Nat.Prime 196987093081 := by
  apply lucas_primality 196987093081 (17 : ZMod 196987093081)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1641559109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1641559109, 1)] : List FactorBlock).map factorBlockValue).prod) = 196987093081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_1641559109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 196987093081) ^ 98493546540 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 196987093081) ^ 65662364360 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 196987093081) ^ 39397418616 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 196987093081) ^ 120 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_238746470311 : Nat.Prime 238746470311 := by
  apply lucas_primality 238746470311 (13 : ZMod 238746470311)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (109, 1), (24337051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (109, 1), (24337051, 1)] : List FactorBlock).map factorBlockValue).prod) = 238746470311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_109
      · exact prime_nineteenQ_24337051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 238746470311) ^ 119373235155 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 79582156770 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 47749294062 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 2190334590 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 238746470311) ^ 9810 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_304575402293 : Nat.Prime 304575402293 := by
  apply lucas_primality 304575402293 (2 : ZMod 304575402293)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (419, 1), (1759, 1), (14759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (419, 1), (1759, 1), (14759, 1)] : List FactorBlock).map factorBlockValue).prod) = 304575402293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_419
      · exact prime_nineteenQ_1759
      · exact prime_nineteenQ_14759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 304575402293) ^ 152287701146 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 304575402293) ^ 43510771756 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 304575402293) ^ 726910268 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 304575402293) ^ 173152588 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 304575402293) ^ 20636588 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_404430377963 : Nat.Prime 404430377963 := by
  apply lucas_primality 404430377963 (2 : ZMod 404430377963)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2887, 1), (5387951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2887, 1), (5387951, 1)] : List FactorBlock).map factorBlockValue).prod) = 404430377963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_2887
      · exact prime_nineteenQ_5387951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 404430377963) ^ 202215188981 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 404430377963) ^ 31110029074 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 404430377963) ^ 140086726 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 404430377963) ^ 75062 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_451884354773 : Nat.Prime 451884354773 := by
  apply lucas_primality 451884354773 (2 : ZMod 451884354773)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (112971088693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (112971088693, 1)] : List FactorBlock).map factorBlockValue).prod) = 451884354773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_112971088693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 451884354773) ^ 225942177386 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 451884354773) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_397
      · exact prime_nineteenQ_2531
      · exact prime_nineteenQ_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_622352498029 : Nat.Prime 622352498029 := by
  apply lucas_primality 622352498029 (2 : ZMod 622352498029)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (51862708169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (51862708169, 1)] : List FactorBlock).map factorBlockValue).prod) = 622352498029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_51862708169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 622352498029) ^ 311176249014 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 622352498029) ^ 207450832676 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 622352498029) ^ 12 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1065502430449 : Nat.Prime 1065502430449 := by
  apply lucas_primality 1065502430449 (11 : ZMod 1065502430449)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (283, 1), (78438047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (283, 1), (78438047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065502430449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_283
      · exact prime_nineteenQ_78438047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1065502430449) ^ 532751215224 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1065502430449) ^ 355167476816 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1065502430449) ^ 3765026256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1065502430449) ^ 13584 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1079762364433 : Nat.Prime 1079762364433 := by
  apply lucas_primality 1079762364433 (10 : ZMod 1079762364433)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (1913, 1), (206299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (1913, 1), (206299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079762364433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_1913
      · exact prime_nineteenQ_206299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1079762364433) ^ 539881182216 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1079762364433) ^ 359920788144 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1079762364433) ^ 56829598128 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1079762364433) ^ 564434064 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1079762364433) ^ 5233968 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1341469855087 : Nat.Prime 1341469855087 := by
  apply lucas_primality 1341469855087 (5 : ZMod 1341469855087)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (28097, 1), (29363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (28097, 1), (29363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1341469855087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_271
      · exact prime_nineteenQ_28097
      · exact prime_nineteenQ_29363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1341469855087) ^ 670734927543 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1341469855087) ^ 447156618362 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1341469855087) ^ 4950073266 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1341469855087) ^ 47744238 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1341469855087) ^ 45685722 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1362758230003 : Nat.Prime 1362758230003 := by
  apply lucas_primality 1362758230003 (3 : ZMod 1362758230003)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (3767, 1), (87509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (3767, 1), (87509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362758230003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_3767
      · exact prime_nineteenQ_87509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1362758230003) ^ 681379115001 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362758230003) ^ 454252743334 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362758230003) ^ 104827556154 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362758230003) ^ 25712419434 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362758230003) ^ 361762206 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362758230003) ^ 15572778 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_35279
      · exact prime_nineteenQ_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2079119063237 : Nat.Prime 2079119063237 := by
  apply lucas_primality 2079119063237 (2 : ZMod 2079119063237)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139939, 1), (3714331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139939, 1), (3714331, 1)] : List FactorBlock).map factorBlockValue).prod) = 2079119063237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_139939
      · exact prime_nineteenQ_3714331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2079119063237) ^ 1039559531618 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2079119063237) ^ 14857324 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2079119063237) ^ 559756 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2740782084259 : Nat.Prime 2740782084259 := by
  apply lucas_primality 2740782084259 (2 : ZMod 2740782084259)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (6599, 1), (3009659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (6599, 1), (3009659, 1)] : List FactorBlock).map factorBlockValue).prod) = 2740782084259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_6599
      · exact prime_nineteenQ_3009659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2740782084259) ^ 1370391042129 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2740782084259) ^ 913594028086 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2740782084259) ^ 119164438446 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2740782084259) ^ 415332942 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2740782084259) ^ 910662 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_4307955470017 : Nat.Prime 4307955470017 := by
  apply lucas_primality 4307955470017 (5 : ZMod 4307955470017)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (83, 1), (1867, 1), (13163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (83, 1), (1867, 1), (13163, 1)] : List FactorBlock).map factorBlockValue).prod) = 4307955470017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_83
      · exact prime_nineteenQ_1867
      · exact prime_nineteenQ_13163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4307955470017) ^ 2153977735008 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307955470017) ^ 1435985156672 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307955470017) ^ 391632315456 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307955470017) ^ 51903077952 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307955470017) ^ 2307421248 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307955470017) ^ 327277632 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_4319049457733 : Nat.Prime 4319049457733 := by
  apply lucas_primality 4319049457733 (2 : ZMod 4319049457733)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1079762364433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1079762364433, 1)] : List FactorBlock).map factorBlockValue).prod) = 4319049457733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_1079762364433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4319049457733) ^ 2159524728866 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4319049457733) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_6147094629469 : Nat.Prime 6147094629469 := by
  apply lucas_primality 6147094629469 (2 : ZMod 6147094629469)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (8521, 1), (4624393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (8521, 1), (4624393, 1)] : List FactorBlock).map factorBlockValue).prod) = 6147094629469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_8521
      · exact prime_nineteenQ_4624393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6147094629469) ^ 3073547314734 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 2049031543156 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 472853433036 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 721405308 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6147094629469) ^ 1329276 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_6684901168709 : Nat.Prime 6684901168709 := by
  apply lucas_primality 6684901168709 (2 : ZMod 6684901168709)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (238746470311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (238746470311, 1)] : List FactorBlock).map factorBlockValue).prod) = 6684901168709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_238746470311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6684901168709) ^ 3342450584354 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6684901168709) ^ 954985881244 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6684901168709) ^ 28 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_9147944801119 : Nat.Prime 9147944801119 := by
  apply lucas_primality 9147944801119 (3 : ZMod 9147944801119)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (7899779621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (7899779621, 1)] : List FactorBlock).map factorBlockValue).prod) = 9147944801119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_193
      · exact prime_nineteenQ_7899779621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9147944801119) ^ 4573972400559 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9147944801119) ^ 3049314933706 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9147944801119) ^ 47398677726 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9147944801119) ^ 1158 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_9231510145621 : Nat.Prime 9231510145621 := by
  apply lucas_primality 9231510145621 (2 : ZMod 9231510145621)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (59629, 1), (368609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (59629, 1), (368609, 1)] : List FactorBlock).map factorBlockValue).prod) = 9231510145621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_59629
      · exact prime_nineteenQ_368609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9231510145621) ^ 4615755072810 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 3077170048540 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 1846302029124 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 1318787163660 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 154815780 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231510145621) ^ 25044180 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_10963128337037 : Nat.Prime 10963128337037 := by
  apply lucas_primality 10963128337037 (2 : ZMod 10963128337037)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2740782084259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2740782084259, 1)] : List FactorBlock).map factorBlockValue).prod) = 10963128337037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_2740782084259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10963128337037) ^ 5481564168518 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10963128337037) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_16364193510881 : Nat.Prime 16364193510881 := by
  apply lucas_primality 16364193510881 (6 : ZMod 16364193510881)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (182131, 1), (561553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (182131, 1), (561553, 1)] : List FactorBlock).map factorBlockValue).prod) = 16364193510881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_182131
      · exact prime_nineteenQ_561553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 16364193510881) ^ 8182096755440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16364193510881) ^ 3272838702176 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16364193510881) ^ 89848480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 16364193510881) ^ 29140960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_16377509992313 : Nat.Prime 16377509992313 := by
  apply lucas_primality 16377509992313 (5 : ZMod 16377509992313)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (331, 1), (7687, 1), (114941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (331, 1), (7687, 1), (114941, 1)] : List FactorBlock).map factorBlockValue).prod) = 16377509992313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_331
      · exact prime_nineteenQ_7687
      · exact prime_nineteenQ_114941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16377509992313) ^ 8188754996156 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 16377509992313) ^ 2339644284616 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 16377509992313) ^ 49478882152 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 16377509992313) ^ 2130546376 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 16377509992313) ^ 142486232 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_18105526433257 : Nat.Prime 18105526433257 := by
  apply lucas_primality 18105526433257 (5 : ZMod 18105526433257)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (63197, 1), (11937227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (63197, 1), (11937227, 1)] : List FactorBlock).map factorBlockValue).prod) = 18105526433257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_63197
      · exact prime_nineteenQ_11937227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18105526433257) ^ 9052763216628 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18105526433257) ^ 6035175477752 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18105526433257) ^ 286493448 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18105526433257) ^ 1516728 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_19106640549727 : Nat.Prime 19106640549727 := by
  apply lucas_primality 19106640549727 (3 : ZMod 19106640549727)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (23369, 1), (5924683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (23369, 1), (5924683, 1)] : List FactorBlock).map factorBlockValue).prod) = 19106640549727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_23369
      · exact prime_nineteenQ_5924683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19106640549727) ^ 9553320274863 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19106640549727) ^ 6368880183242 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19106640549727) ^ 830723502162 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19106640549727) ^ 817606254 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19106640549727) ^ 3224922 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_21415214170873 : Nat.Prime 21415214170873 := by
  apply lucas_primality 21415214170873 (7 : ZMod 21415214170873)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2293, 1), (129713707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2293, 1), (129713707, 1)] : List FactorBlock).map factorBlockValue).prod) = 21415214170873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_2293
      · exact prime_nineteenQ_129713707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 21415214170873) ^ 10707607085436 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 21415214170873) ^ 7138404723624 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 21415214170873) ^ 9339386904 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 21415214170873) ^ 165096 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_28560085672049 : Nat.Prime 28560085672049 := by
  apply lucas_primality 28560085672049 (3 : ZMod 28560085672049)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (68483, 1), (195977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (68483, 1), (195977, 1)] : List FactorBlock).map factorBlockValue).prod) = 28560085672049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_68483
      · exact prime_nineteenQ_195977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28560085672049) ^ 14280042836024 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 28560085672049) ^ 4080012238864 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 28560085672049) ^ 1503162403792 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 28560085672049) ^ 417039056 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 28560085672049) ^ 145731824 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_28576857822509 : Nat.Prime 28576857822509 := by
  apply lucas_primality 28576857822509 (2 : ZMod 28576857822509)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (239, 1), (1663, 1), (131203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (239, 1), (1663, 1), (131203, 1)] : List FactorBlock).map factorBlockValue).prod) = 28576857822509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_137
      · exact prime_nineteenQ_239
      · exact prime_nineteenQ_1663
      · exact prime_nineteenQ_131203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28576857822509) ^ 14288428911254 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 208590203084 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 119568442772 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 17183919316 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 28576857822509) ^ 217806436 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_31689191359339 : Nat.Prime 31689191359339 := by
  apply lucas_primality 31689191359339 (2 : ZMod 31689191359339)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (560929, 1), (9415687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (560929, 1), (9415687, 1)] : List FactorBlock).map factorBlockValue).prod) = 31689191359339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_560929
      · exact prime_nineteenQ_9415687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31689191359339) ^ 15844595679669 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 31689191359339) ^ 10563063786446 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 31689191359339) ^ 56494122 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 31689191359339) ^ 3365574 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_32121988010377 : Nat.Prime 32121988010377 := by
  apply lucas_primality 32121988010377 (13 : ZMod 32121988010377)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (273641, 1), (444649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (273641, 1), (444649, 1)] : List FactorBlock).map factorBlockValue).prod) = 32121988010377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_273641
      · exact prime_nineteenQ_444649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 32121988010377) ^ 16060994005188 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 32121988010377) ^ 10707329336792 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 32121988010377) ^ 2920180728216 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 32121988010377) ^ 117387336 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 32121988010377) ^ 72241224 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_34440719883793 : Nat.Prime 34440719883793 := by
  apply lucas_primality 34440719883793 (10 : ZMod 34440719883793)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (2621, 1), (14408221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (2621, 1), (14408221, 1)] : List FactorBlock).map factorBlockValue).prod) = 34440719883793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_2621
      · exact prime_nineteenQ_14408221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 34440719883793) ^ 17220359941896 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 11480239961264 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 1812669467568 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 13140297552 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 34440719883793) ^ 2390352 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_34880267703949 : Nat.Prime 34880267703949 := by
  apply lucas_primality 34880267703949 (2 : ZMod 34880267703949)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (379, 1), (7669364051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (379, 1), (7669364051, 1)] : List FactorBlock).map factorBlockValue).prod) = 34880267703949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_379
      · exact prime_nineteenQ_7669364051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34880267703949) ^ 17440133851974 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34880267703949) ^ 11626755901316 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34880267703949) ^ 92032368612 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34880267703949) ^ 4548 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_47158448706709 : Nat.Prime 47158448706709 := by
  apply lucas_primality 47158448706709 (2 : ZMod 47158448706709)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (8599279487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (8599279487, 1)] : List FactorBlock).map factorBlockValue).prod) = 47158448706709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_457
      · exact prime_nineteenQ_8599279487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47158448706709) ^ 23579224353354 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 47158448706709) ^ 15719482902236 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 47158448706709) ^ 103191353844 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 47158448706709) ^ 5484 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_55550360248843 : Nat.Prime 55550360248843 := by
  apply lucas_primality 55550360248843 (2 : ZMod 55550360248843)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (196987093081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (196987093081, 1)] : List FactorBlock).map factorBlockValue).prod) = 55550360248843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_196987093081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55550360248843) ^ 27775180124421 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55550360248843) ^ 18516786749614 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55550360248843) ^ 1181922558486 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55550360248843) ^ 282 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_76294320034637 : Nat.Prime 76294320034637 := by
  apply lucas_primality 76294320034637 (2 : ZMod 76294320034637)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (23, 1), (29, 1), (8387, 1), (18233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (23, 1), (29, 1), (8387, 1), (18233, 1)] : List FactorBlock).map factorBlockValue).prod) = 76294320034637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_8387
      · exact prime_nineteenQ_18233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76294320034637) ^ 38147160017318 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 6935847275876 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 4487901178508 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 3317144349332 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 2630838621884 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 9096735428 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 76294320034637) ^ 4184408492 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_82554433057997 : Nat.Prime 82554433057997 := by
  apply lucas_primality 82554433057997 (2 : ZMod 82554433057997)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (51481, 1), (400897579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (51481, 1), (400897579, 1)] : List FactorBlock).map factorBlockValue).prod) = 82554433057997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_51481
      · exact prime_nineteenQ_400897579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82554433057997) ^ 41277216528998 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82554433057997) ^ 1603590316 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82554433057997) ^ 205924 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_101951708986613 : Nat.Prime 101951708986613 := by
  apply lucas_primality 101951708986613 (2 : ZMod 101951708986613)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1341469855087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1341469855087, 1)] : List FactorBlock).map factorBlockValue).prod) = 101951708986613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_1341469855087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 101951708986613) ^ 50975854493306 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 101951708986613) ^ 5365879420348 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 101951708986613) ^ 76 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_107293428600521 : Nat.Prime 107293428600521 := by
  apply lucas_primality 107293428600521 (3 : ZMod 107293428600521)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (449, 1), (19489, 1), (306533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (449, 1), (19489, 1), (306533, 1)] : List FactorBlock).map factorBlockValue).prod) = 107293428600521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_449
      · exact prime_nineteenQ_19489
      · exact prime_nineteenQ_306533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107293428600521) ^ 53646714300260 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 21458685720104 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 238960865480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 5505332680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 107293428600521) ^ 350022440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_123009300652699 : Nat.Prime 123009300652699 := by
  apply lucas_primality 123009300652699 (2 : ZMod 123009300652699)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (137, 1), (16627372351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (137, 1), (16627372351, 1)] : List FactorBlock).map factorBlockValue).prod) = 123009300652699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_137
      · exact prime_nineteenQ_16627372351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123009300652699) ^ 61504650326349 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 123009300652699) ^ 41003100217566 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 123009300652699) ^ 897878106954 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 123009300652699) ^ 7398 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_141598139481229 : Nat.Prime 141598139481229 := by
  apply lucas_primality 141598139481229 (2 : ZMod 141598139481229)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (691, 1), (254872777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (691, 1), (254872777, 1)] : List FactorBlock).map factorBlockValue).prod) = 141598139481229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_691
      · exact prime_nineteenQ_254872777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141598139481229) ^ 70799069740614 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 47199379827076 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 2113405066884 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 204917712708 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 141598139481229) ^ 555564 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_153483796718519 : Nat.Prime 153483796718519 := by
  apply lucas_primality 153483796718519 (7 : ZMod 153483796718519)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (10963128337037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (10963128337037, 1)] : List FactorBlock).map factorBlockValue).prod) = 153483796718519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_10963128337037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 153483796718519) ^ 76741898359259 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 153483796718519) ^ 21926256674074 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 153483796718519) ^ 14 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_176640763490393 : Nat.Prime 176640763490393 := by
  apply lucas_primality 176640763490393 (3 : ZMod 176640763490393)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (137, 1), (743, 1), (11416631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (137, 1), (743, 1), (11416631, 1)] : List FactorBlock).map factorBlockValue).prod) = 176640763490393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_137
      · exact prime_nineteenQ_743
      · exact prime_nineteenQ_11416631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 176640763490393) ^ 88320381745196 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 9296882288968 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 1289348638616 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 237739923944 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 176640763490393) ^ 15472232 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_193340264938297 : Nat.Prime 193340264938297 := by
  apply lucas_primality 193340264938297 (10 : ZMod 193340264938297)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2531, 1), (454695737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2531, 1), (454695737, 1)] : List FactorBlock).map factorBlockValue).prod) = 193340264938297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_2531
      · exact prime_nineteenQ_454695737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 193340264938297) ^ 96670132469148 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 64446754979432 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 27620037848328 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 76388883816 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 193340264938297) ^ 425208 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_206658187604573 : Nat.Prime 206658187604573 := by
  apply lucas_primality 206658187604573 (2 : ZMod 206658187604573)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (354469, 1), (13250177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (354469, 1), (13250177, 1)] : List FactorBlock).map factorBlockValue).prod) = 206658187604573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_354469
      · exact prime_nineteenQ_13250177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 206658187604573) ^ 103329093802286 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 206658187604573) ^ 18787107964052 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 206658187604573) ^ 583007788 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 206658187604573) ^ 15596636 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_258482284077389 : Nat.Prime 258482284077389 := by
  apply lucas_primality 258482284077389 (2 : ZMod 258482284077389)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (9231510145621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (9231510145621, 1)] : List FactorBlock).map factorBlockValue).prod) = 258482284077389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_9231510145621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 258482284077389) ^ 129241142038694 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 258482284077389) ^ 36926040582484 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 258482284077389) ^ 28 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_266699316747293 : Nat.Prime 266699316747293 := by
  apply lucas_primality 266699316747293 (3 : ZMod 266699316747293)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (163, 1), (2860475747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (163, 1), (2860475747, 1)] : List FactorBlock).map factorBlockValue).prod) = 266699316747293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_163
      · exact prime_nineteenQ_2860475747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 266699316747293) ^ 133349658373646 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 266699316747293) ^ 24245392431572 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 266699316747293) ^ 20515332057484 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 266699316747293) ^ 1636192127284 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 266699316747293) ^ 93236 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_344121459783347 : Nat.Prime 344121459783347 := by
  apply lucas_primality 344121459783347 (2 : ZMod 344121459783347)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (311, 1), (9109, 1), (1239523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (311, 1), (9109, 1), (1239523, 1)] : List FactorBlock).map factorBlockValue).prod) = 344121459783347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_311
      · exact prime_nineteenQ_9109
      · exact prime_nineteenQ_1239523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 344121459783347) ^ 172060729891673 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 49160208540478 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 1106499870686 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 37778181994 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 344121459783347) ^ 277624102 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_28807
      · exact prime_nineteenQ_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_520734537703487 : Nat.Prime 520734537703487 := by
  apply lucas_primality 520734537703487 (5 : ZMod 520734537703487)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2269, 1), (42641, 1), (2691067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2269, 1), (42641, 1), (2691067, 1)] : List FactorBlock).map factorBlockValue).prod) = 520734537703487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_2269
      · exact prime_nineteenQ_42641
      · exact prime_nineteenQ_2691067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 520734537703487) ^ 260367268851743 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 520734537703487) ^ 229499575894 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 520734537703487) ^ 12212062046 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 520734537703487) ^ 193504858 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_726327468489479 : Nat.Prime 726327468489479 := by
  apply lucas_primality 726327468489479 (19 : ZMod 726327468489479)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (1301, 1), (2197968457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (1301, 1), (2197968457, 1)] : List FactorBlock).map factorBlockValue).prod) = 726327468489479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_127
      · exact prime_nineteenQ_1301
      · exact prime_nineteenQ_2197968457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 726327468489479) ^ 363163734244739 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (19 : ZMod 726327468489479) ^ 5719113925114 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (19 : ZMod 726327468489479) ^ 558283988078 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (19 : ZMod 726327468489479) ^ 330454 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_823331149041853 : Nat.Prime 823331149041853 := by
  apply lucas_primality 823331149041853 (2 : ZMod 823331149041853)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (2079119063237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (2079119063237, 1)] : List FactorBlock).map factorBlockValue).prod) = 823331149041853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_2079119063237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 823331149041853) ^ 411665574520926 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 823331149041853) ^ 274443716347284 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 823331149041853) ^ 74848286276532 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 823331149041853) ^ 396 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_899415664290557 : Nat.Prime 899415664290557 := by
  apply lucas_primality 899415664290557 (3 : ZMod 899415664290557)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (32121988010377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (32121988010377, 1)] : List FactorBlock).map factorBlockValue).prod) = 899415664290557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_32121988010377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 899415664290557) ^ 449707832145278 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 899415664290557) ^ 128487952041508 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 899415664290557) ^ 28 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1593021709462681 : Nat.Prime 1593021709462681 := by
  apply lucas_primality 1593021709462681 (34 : ZMod 1593021709462681)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (29, 1), (21798326621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (29, 1), (21798326621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1593021709462681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_21798326621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 1593021709462681) ^ 796510854731340 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 1593021709462681) ^ 531007236487560 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 1593021709462681) ^ 318604341892536 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 1593021709462681) ^ 227574529923240 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 1593021709462681) ^ 54931783084920 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (34 : ZMod 1593021709462681) ^ 73080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1676088296946121 : Nat.Prime 1676088296946121 := by
  apply lucas_primality 1676088296946121 (23 : ZMod 1676088296946121)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (79, 1), (31387, 1), (296473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (79, 1), (31387, 1), (296473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1676088296946121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_79
      · exact prime_nineteenQ_31387
      · exact prime_nineteenQ_296473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1676088296946121) ^ 838044148473060 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (23 : ZMod 1676088296946121) ^ 558696098982040 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (23 : ZMod 1676088296946121) ^ 335217659389224 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (23 : ZMod 1676088296946121) ^ 88215173523480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (23 : ZMod 1676088296946121) ^ 21216307556280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (23 : ZMod 1676088296946121) ^ 53400716760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (23 : ZMod 1676088296946121) ^ 5653426440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2723405555631641 : Nat.Prime 2723405555631641 := by
  apply lucas_primality 2723405555631641 (3 : ZMod 2723405555631641)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (127, 1), (233, 1), (19015481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (127, 1), (233, 1), (19015481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2723405555631641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_127
      · exact prime_nineteenQ_233
      · exact prime_nineteenQ_19015481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2723405555631641) ^ 1361702777815820 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 544681111126328 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 247582323239240 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 21444138233320 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 11688435861080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723405555631641) ^ 143220440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_3400354777907569 : Nat.Prime 3400354777907569 := by
  apply lucas_primality 3400354777907569 (14 : ZMod 3400354777907569)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (2671, 1), (36551, 1), (55817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (2671, 1), (36551, 1), (55817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3400354777907569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_2671
      · exact prime_nineteenQ_36551
      · exact prime_nineteenQ_55817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 3400354777907569) ^ 1700177388953784 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 3400354777907569) ^ 1133451592635856 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 3400354777907569) ^ 261565752146736 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 3400354777907569) ^ 1273064312208 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 3400354777907569) ^ 93030417168 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 3400354777907569) ^ 60919697904 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_4407245885620427 : Nat.Prime 4407245885620427 := by
  apply lucas_primality 4407245885620427 (2 : ZMod 4407245885620427)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (126613, 1), (17404397201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (126613, 1), (17404397201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4407245885620427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_126613
      · exact prime_nineteenQ_17404397201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4407245885620427) ^ 2203622942810213 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407245885620427) ^ 34808794402 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407245885620427) ^ 253226 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_6860865944202667 : Nat.Prime 6860865944202667 := by
  apply lucas_primality 6860865944202667 (2 : ZMod 6860865944202667)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 2), (149, 1), (21191, 1), (91199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 2), (149, 1), (21191, 1), (91199, 1)] : List FactorBlock).map factorBlockValue).prod) = 6860865944202667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_149
      · exact prime_nineteenQ_21191
      · exact prime_nineteenQ_91199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6860865944202667) ^ 3430432972101333 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 2286955314734222 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 623715085836606 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 361098207589614 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 46046080162434 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 323763198726 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6860865944202667) ^ 75229618134 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_7568356633535251 : Nat.Prime 7568356633535251 := by
  apply lucas_primality 7568356633535251 (11 : ZMod 7568356633535251)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 3), (7, 2), (19, 1), (23, 1), (52362491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 3), (7, 2), (19, 1), (23, 1), (52362491, 1)] : List FactorBlock).map factorBlockValue).prod) = 7568356633535251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_52362491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7568356633535251) ^ 3784178316767625 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 2522785544511750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 1513671326707050 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 1081193804790750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 398334559659750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 329058984066750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7568356633535251) ^ 144537750 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_12321433103383177 : Nat.Prime 12321433103383177 := by
  apply lucas_primality 12321433103383177 (5 : ZMod 12321433103383177)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (71, 1), (709, 1), (829, 1), (286103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (71, 1), (709, 1), (829, 1), (286103, 1)] : List FactorBlock).map factorBlockValue).prod) = 12321433103383177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_71
      · exact prime_nineteenQ_709
      · exact prime_nineteenQ_829
      · exact prime_nineteenQ_286103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12321433103383177) ^ 6160716551691588 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 4107144367794392 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 286544955892632 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 173541311315256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 17378608044264 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 14863007362344 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12321433103383177) ^ 43066423992 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_12976782109454353 : Nat.Prime 12976782109454353 := by
  apply lucas_primality 12976782109454353 (10 : ZMod 12976782109454353)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (107, 1), (109, 1), (211, 1), (499, 1), (4493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (107, 1), (109, 1), (211, 1), (499, 1), (4493, 1)] : List FactorBlock).map factorBlockValue).prod) = 12976782109454353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_107
      · exact prime_nineteenQ_109
      · exact prime_nineteenQ_211
      · exact prime_nineteenQ_499
      · exact prime_nineteenQ_4493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 12976782109454353) ^ 6488391054727176 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 4325594036484784 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 1853826015636336 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 121278337471536 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 119053046875728 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 61501337011632 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 26005575369648 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 12976782109454353) ^ 2888222147664 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_18310593298496879 : Nat.Prime 18310593298496879 := by
  apply lucas_primality 18310593298496879 (7 : ZMod 18310593298496879)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5531677, 1), (1655067107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5531677, 1), (1655067107, 1)] : List FactorBlock).map factorBlockValue).prod) = 18310593298496879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5531677
      · exact prime_nineteenQ_1655067107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 18310593298496879) ^ 9155296649248439 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 18310593298496879) ^ 3310134214 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 18310593298496879) ^ 11063354 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_20185016378084483 : Nat.Prime 20185016378084483 := by
  apply lucas_primality 20185016378084483 (2 : ZMod 20185016378084483)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5612447, 1), (94644037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5612447, 1), (94644037, 1)] : List FactorBlock).map factorBlockValue).prod) = 20185016378084483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_5612447
      · exact prime_nineteenQ_94644037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20185016378084483) ^ 10092508189042241 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20185016378084483) ^ 1062369283057078 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20185016378084483) ^ 3596473406 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20185016378084483) ^ 213272986 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_20398832627253083 : Nat.Prime 20398832627253083 := by
  apply lucas_primality 20398832627253083 (2 : ZMod 20398832627253083)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57493, 1), (177402750137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57493, 1), (177402750137, 1)] : List FactorBlock).map factorBlockValue).prod) = 20398832627253083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_57493
      · exact prime_nineteenQ_177402750137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20398832627253083) ^ 10199416313626541 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20398832627253083) ^ 354805500274 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20398832627253083) ^ 114986 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_40370032756168967 : Nat.Prime 40370032756168967 := by
  apply lucas_primality 40370032756168967 (5 : ZMod 40370032756168967)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20185016378084483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20185016378084483, 1)] : List FactorBlock).map factorBlockValue).prod) = 40370032756168967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_20185016378084483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 40370032756168967) ^ 20185016378084483 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 40370032756168967) ^ 2 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_46627893857328739 : Nat.Prime 46627893857328739 := by
  apply lucas_primality 46627893857328739 (2 : ZMod 46627893857328739)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12487, 1), (622352498029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12487, 1), (622352498029, 1)] : List FactorBlock).map factorBlockValue).prod) = 46627893857328739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_12487
      · exact prime_nineteenQ_622352498029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46627893857328739) ^ 23313946928664369 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46627893857328739) ^ 15542631285776246 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46627893857328739) ^ 3734114988174 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46627893857328739) ^ 74922 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_60339178690060357 : Nat.Prime 60339178690060357 := by
  apply lucas_primality 60339178690060357 (2 : ZMod 60339178690060357)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1676088296946121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1676088296946121, 1)] : List FactorBlock).map factorBlockValue).prod) = 60339178690060357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_1676088296946121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60339178690060357) ^ 30169589345030178 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60339178690060357) ^ 20113059563353452 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60339178690060357) ^ 36 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_62602229356139021 : Nat.Prime 62602229356139021 := by
  apply lucas_primality 62602229356139021 (2 : ZMod 62602229356139021)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11704607, 1), (267425593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11704607, 1), (267425593, 1)] : List FactorBlock).map factorBlockValue).prod) = 62602229356139021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_11704607
      · exact prime_nineteenQ_267425593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62602229356139021) ^ 31301114678069510 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 62602229356139021) ^ 12520445871227804 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 62602229356139021) ^ 5348511860 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 62602229356139021) ^ 234092140 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_64662795067204513 : Nat.Prime 64662795067204513 := by
  apply lucas_primality 64662795067204513 (5 : ZMod 64662795067204513)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (40099, 1), (5599231751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (40099, 1), (5599231751, 1)] : List FactorBlock).map factorBlockValue).prod) = 64662795067204513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_40099
      · exact prime_nineteenQ_5599231751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64662795067204513) ^ 32331397533602256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 64662795067204513) ^ 21554265022401504 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 64662795067204513) ^ 1612578744288 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 64662795067204513) ^ 11548512 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_73928598620299063 : Nat.Prime 73928598620299063 := by
  apply lucas_primality 73928598620299063 (5 : ZMod 73928598620299063)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12321433103383177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12321433103383177, 1)] : List FactorBlock).map factorBlockValue).prod) = 73928598620299063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_12321433103383177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73928598620299063) ^ 36964299310149531 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 73928598620299063) ^ 24642866206766354 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 73928598620299063) ^ 6 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_88766539549671349 : Nat.Prime 88766539549671349 := by
  apply lucas_primality 88766539549671349 (2 : ZMod 88766539549671349)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (390581, 1), (6312998353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (390581, 1), (6312998353, 1)] : List FactorBlock).map factorBlockValue).prod) = 88766539549671349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_390581
      · exact prime_nineteenQ_6312998353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88766539549671349) ^ 44383269774835674 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 88766539549671349) ^ 29588846516557116 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 88766539549671349) ^ 227267940708 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 88766539549671349) ^ 14060916 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_92596953856845973 : Nat.Prime 92596953856845973 := by
  apply lucas_primality 92596953856845973 (5 : ZMod 92596953856845973)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2969, 1), (1149233, 1), (2261503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2969, 1), (1149233, 1), (2261503, 1)] : List FactorBlock).map factorBlockValue).prod) = 92596953856845973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_2969
      · exact prime_nineteenQ_1149233
      · exact prime_nineteenQ_2261503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92596953856845973) ^ 46298476928422986 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 92596953856845973) ^ 30865651285615324 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 92596953856845973) ^ 31187926526388 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 92596953856845973) ^ 80572828884 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 92596953856845973) ^ 40944873324 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_94736729819765531 : Nat.Prime 94736729819765531 := by
  apply lucas_primality 94736729819765531 (2 : ZMod 94736729819765531)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (193340264938297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (193340264938297, 1)] : List FactorBlock).map factorBlockValue).prod) = 94736729819765531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_193340264938297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94736729819765531) ^ 47368364909882765 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94736729819765531) ^ 18947345963953106 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94736729819765531) ^ 13533818545680790 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94736729819765531) ^ 490 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_170276640838874851 : Nat.Prime 170276640838874851 := by
  apply lucas_primality 170276640838874851 (12 : ZMod 170276640838874851)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 2), (17, 1), (1362758230003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 2), (17, 1), (1362758230003, 1)] : List FactorBlock).map factorBlockValue).prod) = 170276640838874851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_1362758230003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 170276640838874851) ^ 85138320419437425 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (12 : ZMod 170276640838874851) ^ 56758880279624950 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (12 : ZMod 170276640838874851) ^ 34055328167774970 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (12 : ZMod 170276640838874851) ^ 24325234405553550 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (12 : ZMod 170276640838874851) ^ 10016272990522050 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (12 : ZMod 170276640838874851) ^ 124950 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_171832565055736069 : Nat.Prime 171832565055736069 := by
  apply lucas_primality 171832565055736069 (2 : ZMod 171832565055736069)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1961107, 1), (663789307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1961107, 1), (663789307, 1)] : List FactorBlock).map factorBlockValue).prod) = 171832565055736069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_1961107
      · exact prime_nineteenQ_663789307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171832565055736069) ^ 85916282527868034 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 57277521685245356 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 15621142277794188 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 87620188524 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171832565055736069) ^ 258866124 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_240814399918246243 : Nat.Prime 240814399918246243 := by
  apply lucas_primality 240814399918246243 (3 : ZMod 240814399918246243)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (77929, 1), (2754168409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (77929, 1), (2754168409, 1)] : List FactorBlock).map factorBlockValue).prod) = 240814399918246243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_77929
      · exact prime_nineteenQ_2754168409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 240814399918246243) ^ 120407199959123121 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 80271466639415414 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 21892218174386022 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 14165552936367426 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 3090176954898 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 240814399918246243) ^ 87436338 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_370387815427383893 : Nat.Prime 370387815427383893 := by
  apply lucas_primality 370387815427383893 (2 : ZMod 370387815427383893)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (92596953856845973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (92596953856845973, 1)] : List FactorBlock).map factorBlockValue).prod) = 370387815427383893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_92596953856845973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 370387815427383893) ^ 185193907713691946 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 370387815427383893) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_5037757
      · exact prime_nineteenQ_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_392939951653905329 : Nat.Prime 392939951653905329 := by
  apply lucas_primality 392939951653905329 (3 : ZMod 392939951653905329)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (112624157, 1), (218059319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (112624157, 1), (218059319, 1)] : List FactorBlock).map factorBlockValue).prod) = 392939951653905329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_112624157
      · exact prime_nineteenQ_218059319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 392939951653905329) ^ 196469975826952664 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 392939951653905329) ^ 3488949104 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 392939951653905329) ^ 1801986512 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_426745438376754719 : Nat.Prime 426745438376754719 := by
  apply lucas_primality 426745438376754719 (37 : ZMod 426745438376754719)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (59, 1), (16364193510881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (59, 1), (16364193510881, 1)] : List FactorBlock).map factorBlockValue).prod) = 426745438376754719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_16364193510881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 426745438376754719) ^ 213372719188377359 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (37 : ZMod 426745438376754719) ^ 32826572182827286 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (37 : ZMod 426745438376754719) ^ 25102672845691454 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (37 : ZMod 426745438376754719) ^ 7232973531809402 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (37 : ZMod 426745438376754719) ^ 26078 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_466616061331839893 : Nat.Prime 466616061331839893 := by
  apply lucas_primality 466616061331839893 (2 : ZMod 466616061331839893)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (139, 1), (76294320034637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (139, 1), (76294320034637, 1)] : List FactorBlock).map factorBlockValue).prod) = 466616061331839893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_139
      · exact prime_nineteenQ_76294320034637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 466616061331839893) ^ 233308030665919946 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 466616061331839893) ^ 42419641939258172 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 466616061331839893) ^ 3356950081524028 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 466616061331839893) ^ 6116 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_528182958942494357 : Nat.Prime 528182958942494357 := by
  apply lucas_primality 528182958942494357 (2 : ZMod 528182958942494357)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (21481, 1), (6147094629469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (21481, 1), (6147094629469, 1)] : List FactorBlock).map factorBlockValue).prod) = 528182958942494357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_21481
      · exact prime_nineteenQ_6147094629469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 528182958942494357) ^ 264091479471247178 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 528182958942494357) ^ 24588378517876 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 528182958942494357) ^ 85924 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_61717
      · exact prime_nineteenQ_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_591256368856072237 : Nat.Prime 591256368856072237 := by
  apply lucas_primality 591256368856072237 (6 : ZMod 591256368856072237)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (163, 1), (185233, 1), (1631881507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (163, 1), (185233, 1), (1631881507, 1)] : List FactorBlock).map factorBlockValue).prod) = 591256368856072237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_163
      · exact prime_nineteenQ_185233
      · exact prime_nineteenQ_1631881507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 591256368856072237) ^ 295628184428036118 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 197085456285357412 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 3627339686233572 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 3191960227692 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 591256368856072237) ^ 362315748 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_618941509535129819 : Nat.Prime 618941509535129819 := by
  apply lucas_primality 618941509535129819 (2 : ZMod 618941509535129819)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1087, 1), (210499, 1), (79559329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1087, 1), (210499, 1), (79559329, 1)] : List FactorBlock).map factorBlockValue).prod) = 618941509535129819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_1087
      · exact prime_nineteenQ_210499
      · exact prime_nineteenQ_79559329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 618941509535129819) ^ 309470754767564909 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 36408324090301754 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 569403412635814 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 2940353681182 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 618941509535129819) ^ 7779622042 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_841242296483841983 : Nat.Prime 841242296483841983 := by
  apply lucas_primality 841242296483841983 (5 : ZMod 841242296483841983)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (389, 1), (34880267703949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (389, 1), (34880267703949, 1)] : List FactorBlock).map factorBlockValue).prod) = 841242296483841983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_389
      · exact prime_nineteenQ_34880267703949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 841242296483841983) ^ 420621148241920991 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 841242296483841983) ^ 27136848273672322 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 841242296483841983) ^ 2162576597644838 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 841242296483841983) ^ 24118 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_858232378305983971 : Nat.Prime 858232378305983971 := by
  apply lucas_primality 858232378305983971 (2 : ZMod 858232378305983971)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (61, 1), (907, 1), (57451848793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (61, 1), (907, 1), (57451848793, 1)] : List FactorBlock).map factorBlockValue).prod) = 858232378305983971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_61
      · exact prime_nineteenQ_907
      · exact prime_nineteenQ_57451848793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 858232378305983971) ^ 429116189152991985 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 286077459435327990 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 171646475661196794 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 14069383250917770 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 946231949620710 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 858232378305983971) ^ 14938290 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1111149466697709529 : Nat.Prime 1111149466697709529 := by
  apply lucas_primality 1111149466697709529 (7 : ZMod 1111149466697709529)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (2723405555631641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (2723405555631641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1111149466697709529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_2723405555631641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1111149466697709529) ^ 555574733348854764 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111149466697709529) ^ 370383155565903176 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111149466697709529) ^ 65361733335159384 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111149466697709529) ^ 408 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1264857450787857739 : Nat.Prime 1264857450787857739 := by
  apply lucas_primality 1264857450787857739 (2 : ZMod 1264857450787857739)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (10698629, 1), (148153039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (10698629, 1), (148153039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264857450787857739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_10698629
      · exact prime_nineteenQ_148153039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1264857450787857739) ^ 632428725393928869 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264857450787857739) ^ 421619150262619246 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264857450787857739) ^ 180693921541122534 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264857450787857739) ^ 66571444778308302 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264857450787857739) ^ 118226125122 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264857450787857739) ^ 8537505942 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_5028060202735570549 : Nat.Prime 5028060202735570549 := by
  apply lucas_primality 5028060202735570549 (2 : ZMod 5028060202735570549)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (863, 1), (28560085672049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (863, 1), (28560085672049, 1)] : List FactorBlock).map factorBlockValue).prod) = 5028060202735570549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_863
      · exact prime_nineteenQ_28560085672049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5028060202735570549) ^ 2514030101367785274 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028060202735570549) ^ 1676020067578523516 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028060202735570549) ^ 295768247219739444 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028060202735570549) ^ 5826257477097996 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028060202735570549) ^ 176052 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_5059429803151430957 : Nat.Prime 5059429803151430957 := by
  apply lucas_primality 5059429803151430957 (2 : ZMod 5059429803151430957)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1264857450787857739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1264857450787857739, 1)] : List FactorBlock).map factorBlockValue).prod) = 5059429803151430957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_1264857450787857739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5059429803151430957) ^ 2529714901575715478 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5059429803151430957) ^ 4 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_5657105779451173303 : Nat.Prime 5657105779451173303 := by
  apply lucas_primality 5657105779451173303 (3 : ZMod 5657105779451173303)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6143, 1), (153483796718519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6143, 1), (153483796718519, 1)] : List FactorBlock).map factorBlockValue).prod) = 5657105779451173303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_6143
      · exact prime_nineteenQ_153483796718519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5657105779451173303) ^ 2828552889725586651 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5657105779451173303) ^ 1885701926483724434 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5657105779451173303) ^ 920902780311114 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5657105779451173303) ^ 36858 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_15685020321885266749 : Nat.Prime 15685020321885266749 := by
  apply lucas_primality 15685020321885266749 (7 : ZMod 15685020321885266749)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 1), (636149, 1), (6441014959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 1), (636149, 1), (6441014959, 1)] : List FactorBlock).map factorBlockValue).prod) = 15685020321885266749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_636149
      · exact prime_nineteenQ_6441014959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15685020321885266749) ^ 7842510160942633374 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15685020321885266749) ^ 5228340107295088916 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15685020321885266749) ^ 1425910938353206068 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15685020321885266749) ^ 540862769720181612 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15685020321885266749) ^ 24656205263052 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15685020321885266749) ^ 2435178372 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_18838423939996660673 : Nat.Prime 18838423939996660673 := by
  apply lucas_primality 18838423939996660673 (3 : ZMod 18838423939996660673)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (200867, 1), (660817, 1), (2217557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (200867, 1), (660817, 1), (2217557, 1)] : List FactorBlock).map factorBlockValue).prod) = 18838423939996660673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_200867
      · exact prime_nineteenQ_660817
      · exact prime_nineteenQ_2217557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18838423939996660673) ^ 9419211969998330336 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18838423939996660673) ^ 93785559300416 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18838423939996660673) ^ 28507777402816 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18838423939996660673) ^ 8495125013696 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_126115646936777891989 : Nat.Prime 126115646936777891989 := by
  apply lucas_primality 126115646936777891989 (10 : ZMod 126115646936777891989)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (443, 1), (601, 1), (44587, 1), (7439681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (443, 1), (601, 1), (44587, 1), (7439681, 1)] : List FactorBlock).map factorBlockValue).prod) = 126115646936777891989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_443
      · exact prime_nineteenQ_601
      · exact prime_nineteenQ_44587
      · exact prime_nineteenQ_7439681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 126115646936777891989) ^ 63057823468388945994 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 42038548978925963996 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 18016520990968270284 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 7418567466869287764 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 284685433265864316 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 209843006550379188 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 2828529547553724 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 126115646936777891989) ^ 16951754643348 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_127180047267785796313 : Nat.Prime 127180047267785796313 := by
  apply lucas_primality 127180047267785796313 (5 : ZMod 127180047267785796313)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (175727, 1), (4307955470017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (175727, 1), (4307955470017, 1)] : List FactorBlock).map factorBlockValue).prod) = 127180047267785796313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_175727
      · exact prime_nineteenQ_4307955470017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 127180047267785796313) ^ 63590023633892898156 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 127180047267785796313) ^ 42393349089261932104 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 127180047267785796313) ^ 18168578181112256616 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 127180047267785796313) ^ 723736518962856 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 127180047267785796313) ^ 29522136 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_128592066474141292489 : Nat.Prime 128592066474141292489 := by
  apply lucas_primality 128592066474141292489 (7 : ZMod 128592066474141292489)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (307, 1), (487, 1), (3533, 1), (10143596371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (307, 1), (487, 1), (3533, 1), (10143596371, 1)] : List FactorBlock).map factorBlockValue).prod) = 128592066474141292489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_307
      · exact prime_nineteenQ_487
      · exact prime_nineteenQ_3533
      · exact prime_nineteenQ_10143596371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 128592066474141292489) ^ 64296033237070646244 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 42864022158047097496 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 418866666039548184 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 264049417811378424 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 36397414795964136 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 128592066474141292489) ^ 12677167128 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_171369045757508972531 : Nat.Prime 171369045757508972531 := by
  apply lucas_primality 171369045757508972531 (2 : ZMod 171369045757508972531)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (2621, 1), (344121459783347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (2621, 1), (344121459783347, 1)] : List FactorBlock).map factorBlockValue).prod) = 171369045757508972531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_2621
      · exact prime_nineteenQ_344121459783347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171369045757508972531) ^ 85684522878754486265 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 34273809151501794506 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 9019423460921524870 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 65383077358835930 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171369045757508972531) ^ 497990 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_183386141468582607671 : Nat.Prime 183386141468582607671 := by
  apply lucas_primality 183386141468582607671 (7 : ZMod 183386141468582607671)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (277, 1), (33359, 1), (25121561411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (277, 1), (33359, 1), (25121561411, 1)] : List FactorBlock).map factorBlockValue).prod) = 183386141468582607671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_79
      · exact prime_nineteenQ_277
      · exact prime_nineteenQ_33359
      · exact prime_nineteenQ_25121561411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 183386141468582607671) ^ 91693070734291303835 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 36677228293716521534 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 2321343562893450730 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 662043832016543710 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 5497351283569130 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 183386141468582607671) ^ 7299949970 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_186858651670165057673 : Nat.Prime 186858651670165057673 := by
  apply lucas_primality 186858651670165057673 (3 : ZMod 186858651670165057673)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (653, 1), (2843, 1), (177204535801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (653, 1), (2843, 1), (177204535801, 1)] : List FactorBlock).map factorBlockValue).prod) = 186858651670165057673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_71
      · exact prime_nineteenQ_653
      · exact prime_nineteenQ_2843
      · exact prime_nineteenQ_177204535801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 186858651670165057673) ^ 93429325835082528836 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 2631811995354437432 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 286154137320314024 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 65725871146734104 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 186858651670165057673) ^ 1054480072 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_250483458960529628089 : Nat.Prime 250483458960529628089 := by
  apply lucas_primality 250483458960529628089 (31 : ZMod 250483458960529628089)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (6287, 1), (9973, 1), (4059893807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (6287, 1), (9973, 1), (4059893807, 1)] : List FactorBlock).map factorBlockValue).prod) = 250483458960529628089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_6287
      · exact prime_nineteenQ_9973
      · exact prime_nineteenQ_4059893807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 250483458960529628089) ^ 125241729480264814044 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (31 : ZMod 250483458960529628089) ^ 83494486320176542696 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (31 : ZMod 250483458960529628089) ^ 6109352657573893368 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (31 : ZMod 250483458960529628089) ^ 39841491802215624 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (31 : ZMod 250483458960529628089) ^ 25116159526775256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (31 : ZMod 250483458960529628089) ^ 61697046984 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_266595066891837371881 : Nat.Prime 266595066891837371881 := by
  apply lucas_primality 266595066891837371881 (13 : ZMod 266595066891837371881)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (13331, 1), (55550360248843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (13331, 1), (55550360248843, 1)] : List FactorBlock).map factorBlockValue).prod) = 266595066891837371881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_13331
      · exact prime_nineteenQ_55550360248843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 266595066891837371881) ^ 133297533445918685940 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 266595066891837371881) ^ 88865022297279123960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 266595066891837371881) ^ 53319013378367474376 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 266595066891837371881) ^ 19998129689583480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (13 : ZMod 266595066891837371881) ^ 4799160 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_897784781005376023787 : Nat.Prime 897784781005376023787 := by
  apply lucas_primality 897784781005376023787 (2 : ZMod 897784781005376023787)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (389, 1), (88766539549671349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (389, 1), (88766539549671349, 1)] : List FactorBlock).map factorBlockValue).prod) = 897784781005376023787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_389
      · exact prime_nineteenQ_88766539549671349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 897784781005376023787) ^ 448892390502688011893 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 897784781005376023787) ^ 69060367769644309522 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 897784781005376023787) ^ 2307930028291455074 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 897784781005376023787) ^ 10114 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_107
      · exact prime_nineteenQ_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_3799677595581748729619 : Nat.Prime 3799677595581748729619 := by
  apply lucas_primality 3799677595581748729619 (2 : ZMod 3799677595581748729619)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (242009, 1), (101951708986613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (242009, 1), (101951708986613, 1)] : List FactorBlock).map factorBlockValue).prod) = 3799677595581748729619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_242009
      · exact prime_nineteenQ_101951708986613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3799677595581748729619) ^ 1899838797790874364809 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3799677595581748729619) ^ 542811085083106961374 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3799677595581748729619) ^ 345425235961977157238 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3799677595581748729619) ^ 15700563183938402 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3799677595581748729619) ^ 37269386 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_8343050382369831510029 : Nat.Prime 8343050382369831510029 := by
  apply lucas_primality 8343050382369831510029 (2 : ZMod 8343050382369831510029)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2153, 1), (53225903, 1), (18201107173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2153, 1), (53225903, 1), (18201107173, 1)] : List FactorBlock).map factorBlockValue).prod) = 8343050382369831510029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_2153
      · exact prime_nineteenQ_53225903
      · exact prime_nineteenQ_18201107173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8343050382369831510029) ^ 4171525191184915755014 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8343050382369831510029) ^ 3875081459530808876 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8343050382369831510029) ^ 156747934973876 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8343050382369831510029) ^ 458381476636 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_8419214623126221137479 : Nat.Prime 8419214623126221137479 := by
  apply lucas_primality 8419214623126221137479 (6 : ZMod 8419214623126221137479)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (271, 1), (641, 1), (2699, 1), (96544698707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (271, 1), (641, 1), (2699, 1), (96544698707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8419214623126221137479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_271
      · exact prime_nineteenQ_641
      · exact prime_nineteenQ_2699
      · exact prime_nineteenQ_96544698707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8419214623126221137479) ^ 4209607311563110568739 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8419214623126221137479) ^ 2806404874375407045826 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8419214623126221137479) ^ 271587568487942617338 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8419214623126221137479) ^ 31067212631462070618 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8419214623126221137479) ^ 13134500192084588358 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8419214623126221137479) ^ 3119382965219051922 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8419214623126221137479) ^ 87205353954 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_12074758012653445959791 : Nat.Prime 12074758012653445959791 := by
  apply lucas_primality 12074758012653445959791 (14 : ZMod 12074758012653445959791)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (16333, 1), (73928598620299063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (16333, 1), (73928598620299063, 1)] : List FactorBlock).map factorBlockValue).prod) = 12074758012653445959791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_16333
      · exact prime_nineteenQ_73928598620299063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 12074758012653445959791) ^ 6037379006326722979895 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 12074758012653445959791) ^ 2414951602530689191958 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 12074758012653445959791) ^ 739285986202990630 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (14 : ZMod 12074758012653445959791) ^ 163330 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_12452068472553829032367 : Nat.Prime 12452068472553829032367 := by
  apply lucas_primality 12452068472553829032367 (3 : ZMod 12452068472553829032367)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2467, 1), (841242296483841983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2467, 1), (841242296483841983, 1)] : List FactorBlock).map factorBlockValue).prod) = 12452068472553829032367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_2467
      · exact prime_nineteenQ_841242296483841983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12452068472553829032367) ^ 6226034236276914516183 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452068472553829032367) ^ 4150689490851276344122 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452068472553829032367) ^ 5047453778903051898 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452068472553829032367) ^ 14802 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_14240133936556782272833 : Nat.Prime 14240133936556782272833 := by
  apply lucas_primality 14240133936556782272833 (7 : ZMod 14240133936556782272833)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (89, 1), (97, 1), (733, 1), (1065502430449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (89, 1), (97, 1), (733, 1), (1065502430449, 1)] : List FactorBlock).map factorBlockValue).prod) = 14240133936556782272833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_89
      · exact prime_nineteenQ_97
      · exact prime_nineteenQ_733
      · exact prime_nineteenQ_1065502430449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14240133936556782272833) ^ 7120066968278391136416 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 4746711312185594090944 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 1294557630596071115712 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 160001504905132385088 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 146805504500585384256 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 19427195002123850304 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14240133936556782272833) ^ 13364712768 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_39703327656062808021443 : Nat.Prime 39703327656062808021443 := by
  apply lucas_primality 39703327656062808021443 (2 : ZMod 39703327656062808021443)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1709, 1), (359419759, 1), (32318626891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1709, 1), (359419759, 1), (32318626891, 1)] : List FactorBlock).map factorBlockValue).prod) = 39703327656062808021443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_1709
      · exact prime_nineteenQ_359419759
      · exact prime_nineteenQ_32318626891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39703327656062808021443) ^ 19851663828031404010721 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39703327656062808021443) ^ 23231906176748278538 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39703327656062808021443) ^ 110465066713438 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39703327656062808021443) ^ 1228496736262 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_46384852435292319013777 : Nat.Prime 46384852435292319013777 := by
  apply lucas_primality 46384852435292319013777 (10 : ZMod 46384852435292319013777)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (191, 1), (5059429803151430957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (191, 1), (5059429803151430957, 1)] : List FactorBlock).map factorBlockValue).prod) = 46384852435292319013777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_191
      · exact prime_nineteenQ_5059429803151430957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 46384852435292319013777) ^ 23192426217646159506888 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 46384852435292319013777) ^ 15461617478430773004592 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 46384852435292319013777) ^ 242852630551268685936 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 46384852435292319013777) ^ 9168 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_68403221753129257359241 : Nat.Prime 68403221753129257359241 := by
  apply lucas_primality 68403221753129257359241 (11 : ZMod 68403221753129257359241)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (5, 1), (19, 1), (370387815427383893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (5, 1), (19, 1), (370387815427383893, 1)] : List FactorBlock).map factorBlockValue).prod) = 68403221753129257359241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_370387815427383893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 68403221753129257359241) ^ 34201610876564628679620 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 68403221753129257359241) ^ 22801073917709752453080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 68403221753129257359241) ^ 13680644350625851471848 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 68403221753129257359241) ^ 3600169565954171439960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (11 : ZMod 68403221753129257359241) ^ 184680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_89049766694364876067741 : Nat.Prime 89049766694364876067741 := by
  apply lucas_primality 89049766694364876067741 (2 : ZMod 89049766694364876067741)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (911, 1), (60339178690060357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (911, 1), (60339178690060357, 1)] : List FactorBlock).map factorBlockValue).prod) = 89049766694364876067741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_911
      · exact prime_nineteenQ_60339178690060357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89049766694364876067741) ^ 44524883347182438033870 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89049766694364876067741) ^ 29683255564788292022580 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89049766694364876067741) ^ 17809953338872975213548 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89049766694364876067741) ^ 97749469477897778340 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89049766694364876067741) ^ 1475820 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_128439670184763300109301 : Nat.Prime 128439670184763300109301 := by
  apply lucas_primality 128439670184763300109301 (2 : ZMod 128439670184763300109301)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (397, 1), (170276640838874851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (397, 1), (170276640838874851, 1)] : List FactorBlock).map factorBlockValue).prod) = 128439670184763300109301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_397
      · exact prime_nineteenQ_170276640838874851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 128439670184763300109301) ^ 64219835092381650054650 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 128439670184763300109301) ^ 25687934036952660021860 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 128439670184763300109301) ^ 6759982641303331584700 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 128439670184763300109301) ^ 323525617593862216900 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 128439670184763300109301) ^ 754300 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_208820879214227097291239 : Nat.Prime 208820879214227097291239 := by
  apply lucas_primality 208820879214227097291239 (17 : ZMod 208820879214227097291239)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (2141, 1), (62602229356139021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (2141, 1), (62602229356139021, 1)] : List FactorBlock).map factorBlockValue).prod) = 208820879214227097291239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_2141
      · exact prime_nineteenQ_62602229356139021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 208820879214227097291239) ^ 104410439607113548645619 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 208820879214227097291239) ^ 10990572590222478804802 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 208820879214227097291239) ^ 5093192175956758470518 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 208820879214227097291239) ^ 97534273336864594718 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (17 : ZMod 208820879214227097291239) ^ 3335678 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_239022236860933007190073 : Nat.Prime 239022236860933007190073 := by
  apply lucas_primality 239022236860933007190073 (15 : ZMod 239022236860933007190073)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (43, 1), (139, 1), (18310593298496879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (43, 1), (139, 1), (18310593298496879, 1)] : List FactorBlock).map factorBlockValue).prod) = 239022236860933007190073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_139
      · exact prime_nineteenQ_18310593298496879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 239022236860933007190073) ^ 119511118430466503595036 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 239022236860933007190073) ^ 79674078953644335730024 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 239022236860933007190073) ^ 34146033837276143884296 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 239022236860933007190073) ^ 18386325912379462091544 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 239022236860933007190073) ^ 5558656671184488539304 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 239022236860933007190073) ^ 1719584437848438900648 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (15 : ZMod 239022236860933007190073) ^ 13053768 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_309540861772294272798521 : Nat.Prime 309540861772294272798521 := by
  apply lucas_primality 309540861772294272798521 (3 : ZMod 309540861772294272798521)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 1), (10253, 1), (20398832627253083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 1), (10253, 1), (20398832627253083, 1)] : List FactorBlock).map factorBlockValue).prod) = 309540861772294272798521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_10253
      · exact prime_nineteenQ_20398832627253083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 309540861772294272798521) ^ 154770430886147136399260 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 61908172354458854559704 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 8365969237089034399960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 30190272288334562840 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (3 : ZMod 309540861772294272798521) ^ 15174440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_351018389192012111802917 : Nat.Prime 351018389192012111802917 := by
  apply lucas_primality 351018389192012111802917 (2 : ZMod 351018389192012111802917)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (329039453, 1), (266699316747293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (329039453, 1), (266699316747293, 1)] : List FactorBlock).map factorBlockValue).prod) = 351018389192012111802917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_329039453
      · exact prime_nineteenQ_266699316747293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 351018389192012111802917) ^ 175509194596006055901458 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 351018389192012111802917) ^ 1066797266989172 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 351018389192012111802917) ^ 1316157812 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_591226793650408566687263 : Nat.Prime 591226793650408566687263 := by
  apply lucas_primality 591226793650408566687263 (5 : ZMod 591226793650408566687263)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43086893, 1), (6860865944202667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43086893, 1), (6860865944202667, 1)] : List FactorBlock).map factorBlockValue).prod) = 591226793650408566687263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_43086893
      · exact prime_nineteenQ_6860865944202667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 591226793650408566687263) ^ 295613396825204283343631 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 591226793650408566687263) ^ 13721731888405334 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 591226793650408566687263) ^ 86173786 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_776060487060066439202483 : Nat.Prime 776060487060066439202483 := by
  apply lucas_primality 776060487060066439202483 (2 : ZMod 776060487060066439202483)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (461, 1), (593, 1), (36497, 1), (94167868097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (461, 1), (593, 1), (36497, 1), (94167868097, 1)] : List FactorBlock).map factorBlockValue).prod) = 776060487060066439202483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_461
      · exact prime_nineteenQ_593
      · exact prime_nineteenQ_36497
      · exact prime_nineteenQ_94167868097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 776060487060066439202483) ^ 388030243530033219601241 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 110865783865723777028926 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 13153567577289261681398 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 1683428388416630019962 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 1308702339055761280274 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 21263678851962255506 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 776060487060066439202483) ^ 8241245158706 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1249684049955695303628143 : Nat.Prime 1249684049955695303628143 := by
  apply lucas_primality 1249684049955695303628143 (5 : ZMod 1249684049955695303628143)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1183003, 1), (528182958942494357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1183003, 1), (528182958942494357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249684049955695303628143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_1183003
      · exact prime_nineteenQ_528182958942494357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1249684049955695303628143) ^ 624842024977847651814071 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249684049955695303628143) ^ 1056365917884988714 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249684049955695303628143) ^ 2366006 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1611757967852021459619421 : Nat.Prime 1611757967852021459619421 := by
  apply lucas_primality 1611757967852021459619421 (10 : ZMod 1611757967852021459619421)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (71, 1), (126115646936777891989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (71, 1), (126115646936777891989, 1)] : List FactorBlock).map factorBlockValue).prod) = 1611757967852021459619421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_71
      · exact prime_nineteenQ_126115646936777891989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1611757967852021459619421) ^ 805878983926010729809710 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1611757967852021459619421) ^ 537252655950673819873140 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1611757967852021459619421) ^ 322351593570404291923884 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1611757967852021459619421) ^ 22700816448620020558020 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1611757967852021459619421) ^ 12780 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_3006299624993793239121503 : Nat.Prime 3006299624993793239121503 := by
  apply lucas_primality 3006299624993793239121503 (5 : ZMod 3006299624993793239121503)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52600248139, 1), (28576857822509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52600248139, 1), (28576857822509, 1)] : List FactorBlock).map factorBlockValue).prod) = 3006299624993793239121503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_52600248139
      · exact prime_nineteenQ_28576857822509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3006299624993793239121503) ^ 1503149812496896619560751 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3006299624993793239121503) ^ 57153715645018 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3006299624993793239121503) ^ 105200496278 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_3246108496814107381895357 : Nat.Prime 3246108496814107381895357 := by
  apply lucas_primality 3246108496814107381895357 (2 : ZMod 3246108496814107381895357)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (101, 1), (186858651670165057673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (101, 1), (186858651670165057673, 1)] : List FactorBlock).map factorBlockValue).prod) = 3246108496814107381895357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_101
      · exact prime_nineteenQ_186858651670165057673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3246108496814107381895357) ^ 1623054248407053690947678 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246108496814107381895357) ^ 75490895274746683299892 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246108496814107381895357) ^ 32139688087268389919756 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246108496814107381895357) ^ 17372 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_5649665693650307616377231 : Nat.Prime 5649665693650307616377231 := by
  apply lucas_primality 5649665693650307616377231 (7 : ZMod 5649665693650307616377231)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2129, 1), (2093813, 1), (18105526433257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2129, 1), (2093813, 1), (18105526433257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5649665693650307616377231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_2129
      · exact prime_nineteenQ_2093813
      · exact prime_nineteenQ_18105526433257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5649665693650307616377231) ^ 2824832846825153808188615 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5649665693650307616377231) ^ 1129933138730061523275446 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5649665693650307616377231) ^ 807095099092901088053890 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5649665693650307616377231) ^ 2653671063245799725870 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5649665693650307616377231) ^ 2698266604348290710 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5649665693650307616377231) ^ 312040951390 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_10727349951267250755833749 : Nat.Prime 10727349951267250755833749 := by
  apply lucas_primality 10727349951267250755833749 (2 : ZMod 10727349951267250755833749)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (13009, 1), (253697251, 1), (9340143089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (13009, 1), (253697251, 1), (9340143089, 1)] : List FactorBlock).map factorBlockValue).prod) = 10727349951267250755833749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_13009
      · exact prime_nineteenQ_253697251
      · exact prime_nineteenQ_9340143089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10727349951267250755833749) ^ 5363674975633625377916874 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 3575783317089083585277916 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 369908619009215543304612 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 824609881717830021972 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 42284060662790748 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10727349951267250755833749) ^ 1148520943314132 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_103041609164924876526219589 : Nat.Prime 103041609164924876526219589 := by
  apply lucas_primality 103041609164924876526219589 (2 : ZMod 103041609164924876526219589)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (67, 1), (14240133936556782272833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (67, 1), (14240133936556782272833, 1)] : List FactorBlock).map factorBlockValue).prod) = 103041609164924876526219589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_67
      · exact prime_nineteenQ_14240133936556782272833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103041609164924876526219589) ^ 51520804582462438263109794 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 103041609164924876526219589) ^ 34347203054974958842073196 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 103041609164924876526219589) ^ 1537934465148132485465964 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 103041609164924876526219589) ^ 7236 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_233990320812016907111623651 : Nat.Prime 233990320812016907111623651 := by
  apply lucas_primality 233990320812016907111623651 (2 : ZMod 233990320812016907111623651)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 233990320812016907111623651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 233990320812016907111623651) ^ 116995160406008453555811825 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 77996773604005635703874550 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 46798064162403381422324730 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 33427188687430986730231950 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 21271847346546991555602150 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 17999255447078223623971050 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 13764136518353935712448450 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 12315280042737731953243350 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 10173492209218126396157550 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 8068631752138514038331850 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 7548074864903771197149150 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 6324062724649105597611450 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 5707080995415046514917650 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 5441635367721323421200550 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 4978517464085466108757950 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 4414911713434281266257050 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 3965937640881642493417350 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (2 : ZMod 233990320812016907111623651) ^ 3835906898557654214944650 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_303555010783157068685349601 : Nat.Prime 303555010783157068685349601 := by
  apply lucas_primality 303555010783157068685349601 (83 : ZMod 303555010783157068685349601)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 303555010783157068685349601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 303555010783157068685349601) ^ 151777505391578534342674800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 101185003594385689561783200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 60711002156631413737069920 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 43365001540451009812192800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 27595910071196097153213600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 23350385444858236052719200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 17856177104891592275608800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 15976579514903003615018400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 13198043947093785595015200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 10467414164936450644322400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 9792097122037324796301600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 7403780750808708992325600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 7059418855422257411287200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 6458617250705469546496800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 5727453033644472994063200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 5145000182765374045514400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 303555010783157068685349601) ^ 4976311652182902765333600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_345585704583901893580244161 : Nat.Prime 345585704583901893580244161 := by
  apply lucas_primality 345585704583901893580244161 (71 : ZMod 345585704583901893580244161)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 345585704583901893580244161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 345585704583901893580244161) ^ 172792852291950946790122080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 115195234861300631193414720 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 69117140916780378716048832 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 49369386369128841940034880 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 31416882234900172143658560 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 20328570857876581975308480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 18188721293889573346328640 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 15025465416691386677401920 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 11916748433927651502767040 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 11147925954319415921943360 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 9340154177943294421087680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 8428919623997607160493760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 8036876850788416129773120 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 7352887331572380714473280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 6520484992149092331702720 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 5857384823455964297970240 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 345585704583901893580244161) ^ 5665339419408227763610560 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_368247062261534804634686401 : Nat.Prime 368247062261534804634686401 := by
  apply lucas_primality 368247062261534804634686401 (71 : ZMod 368247062261534804634686401)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 368247062261534804634686401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 368247062261534804634686401) ^ 184123531130767402317343200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 122749020753844934878228800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 73649412452306960926937280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 52606723180219257804955200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 33477005660139527694062400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 28326697097041138818052800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 21661591897737341449099200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 19381424329554463401825600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 16010741837458034984116800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 12698174560742579470161600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 11878937492307574343054400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 9952623304365805530667200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 8981635664915483039870400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 8563885168872902433364800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 7835043877904995843291200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 6948057778519524615748800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (71 : ZMod 368247062261534804634686401) ^ 6241475631551437366689600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_374384513299227051378597841 : Nat.Prime 374384513299227051378597841 := by
  apply lucas_primality 374384513299227051378597841 (67 : ZMod 374384513299227051378597841)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 374384513299227051378597841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 374384513299227051378597841) ^ 187192256649613525689298920 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 124794837766409017126199280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 74876902659845410275719568 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 53483501899889578768371120 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 34034955754475186488963440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 28798808715325157798353680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 22022618429366297139917520 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 19704448068380371125189360 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 16277587534749002233852080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 12909810803421622461330960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 12076919783846033915438640 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 10118500359438568956178320 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 9131329592664074423868240 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 8706616588354117473920880 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 7965627942536745774012720 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 7063858741494850026011280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 6345500225410627989467760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 374384513299227051378597841) ^ 6137451037692246743911440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_680699115089503729779268801 : Nat.Prime 680699115089503729779268801 := by
  apply lucas_primality 680699115089503729779268801 (67 : ZMod 680699115089503729779268801)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 680699115089503729779268801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 680699115089503729779268801) ^ 340349557544751864889634400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 226899705029834576593089600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 136139823017900745955853760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 97242730727071961397038400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 52361470391500286906097600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 40041124417029631163486400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 35826269215237038409435200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 29595613699543640425185600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 23472383278948404475147200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 21958035970629152573524800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 18397273380797398102142400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 16602417441207408043396800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 15830211978825668134401600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 14482959895521355952750400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 12843379529990636410929600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 11537273137110232708123200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (67 : ZMod 680699115089503729779268801) ^ 11159001886713175898020800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_724615187030762034926318401 : Nat.Prime 724615187030762034926318401 := by
  apply lucas_primality 724615187030762034926318401 (62 : ZMod 724615187030762034926318401)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 724615187030762034926318401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (62 : ZMod 724615187030762034926318401) ^ 362307593515381017463159200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 241538395676920678308772800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 144923037406152406985263680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 103516455290108862132331200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 65874107911887457720574400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 55739629771597079609716800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 42624422766515413819195200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 38137641422671686048753600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 31505008131772262388100800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 24986730587267656376769600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 19584194244074649592603200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 17673541147091756949422400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 16851515977459582207588800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 15417344404909830530347200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 13671984660957774243892800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 12281613339504441269937600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (62 : ZMod 724615187030762034926318401) ^ 11878937492307574343054400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1321357105761977828395051201 : Nat.Prime 1321357105761977828395051201 := by
  apply lucas_primality 1321357105761977828395051201 (83 : ZMod 1321357105761977828395051201)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1321357105761977828395051201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1321357105761977828395051201) ^ 660678552880988914197525600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 440452368587325942798350400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 264271421152395565679010240 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 188765300823139689770721600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 120123373251088893490459200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 101642854289382909876542400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 69545110829577780441844800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 57450308946172949060654400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 45564038129723373392932800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 42624422766515413819195200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 35712354209783184551217600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 32228222091755556790123200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 30729235017720414613838400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 28113980973659102731809600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 24931266146452411856510400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 22395883148508098786356800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (83 : ZMod 1321357105761977828395051201) ^ 21661591897737341449099200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1497538053196908205514391361 : Nat.Prime 1497538053196908205514391361 := by
  apply lucas_primality 1497538053196908205514391361 (134 : ZMod 1497538053196908205514391361)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497538053196908205514391361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (134 : ZMod 1497538053196908205514391361) ^ 748769026598454102757195680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 499179351065636068504797120 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 299507610639381641102878272 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 213934007599558315073484480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 136139823017900745955853760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 115195234861300631193414720 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 88090473717465188559670080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 78817792273521484500757440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 65110350138996008935408320 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 51639243213686489845323840 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 48307679135384135661754560 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 40474001437754275824713280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 36525318370656297695472960 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 34826466353416469895683520 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 31862511770146983096050880 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 28255434965979400104045120 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 25382000901642511957871040 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (134 : ZMod 1497538053196908205514391361) ^ 24549804150768986975645760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_1871922566496135256892989201 : Nat.Prime 1871922566496135256892989201 := by
  apply lucas_primality 1871922566496135256892989201 (101 : ZMod 1871922566496135256892989201)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1871922566496135256892989201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1871922566496135256892989201) ^ 935961283248067628446494600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 623974188832045085630996400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 374384513299227051378597840 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 267417509499447893841855600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 170174778772375932444817200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 143994043576625788991768400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 110113092146831485699587600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 98522240341901855625946800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 81387937673745011169260400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 64549054017108112306654800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 60384598919230169577193200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 50592501797192844780891600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 45656647963320372119341200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 43533082941770587369604400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 39828139712683728870063600 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 35319293707474250130056400 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 31727501127053139947338800 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (101 : ZMod 1871922566496135256892989201) ^ 30687255188461233719557200 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_2246307079795362308271587041 : Nat.Prime 2246307079795362308271587041 := by
  apply lucas_primality 2246307079795362308271587041 (73 : ZMod 2246307079795362308271587041)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2246307079795362308271587041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_3
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_11
      · exact prime_nineteenQ_13
      · exact prime_nineteenQ_17
      · exact prime_nineteenQ_19
      · exact prime_nineteenQ_23
      · exact prime_nineteenQ_29
      · exact prime_nineteenQ_31
      · exact prime_nineteenQ_37
      · exact prime_nineteenQ_41
      · exact prime_nineteenQ_43
      · exact prime_nineteenQ_47
      · exact prime_nineteenQ_53
      · exact prime_nineteenQ_59
      · exact prime_nineteenQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 2246307079795362308271587041) ^ 1123153539897681154135793520 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 748769026598454102757195680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 449261415959072461654317408 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 320901011399337472610226720 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 204209734526851118933780640 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 172792852291950946790122080 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 132135710576197782839505120 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 118226688410282226751136160 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 97665525208494013403112480 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 77458864820529734767985760 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 72461518703076203492631840 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 60711002156631413737069920 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 54787977555984446543209440 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 52239699530124704843525280 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 47793767655220474644076320 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 42383152448969100156067680 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 38073001352463767936806560 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (73 : ZMod 2246307079795362308271587041) ^ 36824706226153480463468640 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem prime_nineteenQ_22463070797953623082715870471 : Nat.Prime 22463070797953623082715870471 := by
  apply lucas_primality 22463070797953623082715870471 (7 : ZMod 22463070797953623082715870471)
  · rw [← nineteenQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (131, 1), (503, 1), (14321, 1), (111343009, 1), (3054186173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (131, 1), (503, 1), (14321, 1), (111343009, 1), (3054186173, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nineteenQ_2
      · exact prime_nineteenQ_5
      · exact prime_nineteenQ_7
      · exact prime_nineteenQ_131
      · exact prime_nineteenQ_503
      · exact prime_nineteenQ_14321
      · exact prime_nineteenQ_111343009
      · exact prime_nineteenQ_3054186173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 22463070797953623082715870471) ^ 11231535398976811541357935235 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 4492614159590724616543174094 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 3209010113993374726102267210 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 171473822885142160936762370 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 44658192441259688037208490 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 1568540660425502624308070 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 201746575736547797830 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide
    · change (7 : ZMod 22463070797953623082715870471) ^ 7354846602520331390 ≠ 1
      rw [← nineteenQFastPow_eq_pow]
      decide

private theorem phi_nineteenQ_22463070797953623082715870400 : Nat.totient 22463070797953623082715870400 = 2955856000727852148326400000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 2), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_7, prime_nineteenQ_11, prime_nineteenQ_13, prime_nineteenQ_17, prime_nineteenQ_19, prime_nineteenQ_23, prime_nineteenQ_29, prime_nineteenQ_31, prime_nineteenQ_37, prime_nineteenQ_41, prime_nineteenQ_43, prime_nineteenQ_47, prime_nineteenQ_53, prime_nineteenQ_59, prime_nineteenQ_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870401 : Nat.totient 22463070797953623082715870401 = 22448371843838548766018027520 := by
  rw [← show ((([(1657, 1), (23041, 1), (133499, 1), (4407245885620427, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_1657, prime_nineteenQ_23041, prime_nineteenQ_133499, prime_nineteenQ_4407245885620427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870402 : Nat.totient 22463070797953623082715870402 = 11128493789811886664831715504 := by
  rw [← show ((([(2, 1), (109, 1), (103041609164924876526219589, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_109, prime_nineteenQ_103041609164924876526219589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870403 : Nat.totient 22463070797953623082715870403 = 14975356382453056748250753800 := by
  rw [← show ((([(3, 1), (620111, 1), (12074758012653445959791, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_620111, prime_nineteenQ_12074758012653445959791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870404 : Nat.totient 22463070797953623082715870404 = 11127665875126368910870725120 := by
  rw [← show ((([(2, 2), (113, 1), (2543, 1), (113731, 1), (171832565055736069, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_113, prime_nineteenQ_2543, prime_nineteenQ_113731, prime_nineteenQ_171832565055736069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870405 : Nat.totient 22463070797953623082715870405 = 17969357459235921030373621248 := by
  rw [← show ((([(5, 1), (16349, 1), (12831738653, 1), (21415214170873, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_16349, prime_nineteenQ_12831738653, prime_nineteenQ_21415214170873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870406 : Nat.totient 22463070797953623082715870406 = 7466235566082006526060288608 := by
  rw [← show ((([(2, 1), (3, 1), (349, 1), (10727349951267250755833749, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_349, prime_nineteenQ_10727349951267250755833749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870407 : Nat.totient 22463070797953623082715870407 = 19248965863007791882720089600 := by
  rw [← show ((([(7, 1), (3889, 1), (133781, 1), (619561331, 1), (9955301119, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_7, prime_nineteenQ_3889, prime_nineteenQ_133781, prime_nineteenQ_619561331, prime_nineteenQ_9955301119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870408 : Nat.totient 22463070797953623082715870408 = 11231535396501045485071056016 := by
  rw [← show ((([(2, 3), (4536589979, 1), (618941509535129819, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_4536589979, prime_nineteenQ_618941509535129819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870409 : Nat.totient 22463070797953623082715870409 = 14975086482245734984334630400 := by
  rw [← show ((([(3, 2), (56633, 1), (507641, 1), (158598107, 1), (547396931, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_56633, prime_nineteenQ_507641, prime_nineteenQ_158598107, prime_nineteenQ_547396931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870410 : Nat.totient 22463070797953623082715870410 = 8985228319181449233086348160 := by
  rw [← show ((([(2, 1), (5, 1), (2246307079795362308271587041, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_5, prime_nineteenQ_2246307079795362308271587041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870411 : Nat.totient 22463070797953623082715870411 = 20320469438959065366314553600 := by
  rw [← show ((([(11, 1), (271, 1), (907, 1), (7477, 1), (1111149466697709529, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_11, prime_nineteenQ_271, prime_nineteenQ_907, prime_nineteenQ_7477, prime_nineteenQ_1111149466697709529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870412 : Nat.totient 22463070797953623082715870412 = 7487690265984541027571956800 := by
  rw [← show ((([(2, 2), (3, 1), (1871922566496135256892989201, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_1871922566496135256892989201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870413 : Nat.totient 22463070797953623082715870413 = 20735142275030931608591696448 := by
  rw [← show ((([(13, 1), (6684901168709, 1), (258482284077389, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_13, prime_nineteenQ_6684901168709, prime_nineteenQ_258482284077389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870414 : Nat.totient 22463070797953623082715870414 = 9627030228949580537815805952 := by
  rw [← show ((([(2, 1), (7, 1), (85171937, 1), (18838423939996660673, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_7, prime_nineteenQ_85171937, prime_nineteenQ_18838423939996660673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870415 : Nat.totient 22463070797953623082715870415 = 11980304425575265644115130880 := by
  rw [← show ((([(3, 1), (5, 1), (1497538053196908205514391361, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_1497538053196908205514391361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870416 : Nat.totient 22463070797953623082715870416 = 11207485001976861195444959456 := by
  rw [← show ((([(2, 4), (467, 1), (3006299624993793239121503, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_467, prime_nineteenQ_3006299624993793239121503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870417 : Nat.totient 22463070797953623082715870417 = 21141713692191645254320819200 := by
  rw [← show ((([(17, 1), (1321357105761977828395051201, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_17, prime_nineteenQ_1321357105761977828395051201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870418 : Nat.totient 22463070797953623082715870418 = 7480904611977920533882121280 := by
  rw [← show ((([(2, 1), (3, 2), (1439, 1), (4729, 1), (183386141468582607671, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_1439, prime_nineteenQ_4729, prime_nineteenQ_183386141468582607671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870419 : Nat.totient 22463070797953623082715870419 = 21069986901359321511017571456 := by
  rw [← show ((([(19, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_19, prime_nineteenQ_103, prime_nineteenQ_5009, prime_nineteenQ_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870420 : Nat.totient 22463070797953623082715870420 = 8985228318664146733593563136 := by
  rw [← show ((([(2, 2), (5, 1), (17369393617, 1), (64662795067204513, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_5, prime_nineteenQ_17369393617, prime_nineteenQ_64662795067204513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870421 : Nat.totient 22463070797953623082715870421 = 12835891031151828258459649584 := by
  rw [← show ((([(3, 1), (7, 1), (85903, 1), (12452068472553829032367, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_7, prime_nineteenQ_85903, prime_nineteenQ_12452068472553829032367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870422 : Nat.totient 22463070797953623082715870422 = 10145451779041011004353415920 := by
  rw [← show ((([(2, 1), (11, 2), (157, 1), (591226793650408566687263, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_11, prime_nineteenQ_157, prime_nineteenQ_591226793650408566687263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870423 : Nat.totient 22463070797953623082715870423 = 21464557541236842222675787104 := by
  rw [← show ((([(23, 1), (983, 1), (7016656643, 1), (141598139481229, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_23, prime_nineteenQ_983, prime_nineteenQ_7016656643, prime_nineteenQ_141598139481229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870424 : Nat.totient 22463070797953623082715870424 = 7487683083706292984555426336 := by
  rw [← show ((([(2, 3), (3, 1), (1042523, 1), (897784781005376023787, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_1042523, prime_nineteenQ_897784781005376023787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870425 : Nat.totient 22463070797953623082715870425 = 17945462957363784560100119120 := by
  rw [← show ((([(5, 2), (719, 1), (1249684049955695303628143, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_719, prime_nineteenQ_1249684049955695303628143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870426 : Nat.totient 22463070797953623082715870426 = 10225549407021674731369144704 := by
  rw [← show ((([(2, 1), (13, 1), (73, 1), (49146259, 1), (240814399918246243, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_13, prime_nineteenQ_73, prime_nineteenQ_49146259, prime_nineteenQ_240814399918246243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870427 : Nat.totient 22463070797953623082715870427 = 14975380531832849657057025000 := by
  rw [← show ((([(3, 3), (109926847451, 1), (7568356633535251, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_109926847451, prime_nineteenQ_7568356633535251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870428 : Nat.totient 22463070797953623082715870428 = 9596660801848917394847901120 := by
  rw [← show ((([(2, 2), (7, 1), (317, 1), (26713663, 1), (94736729819765531, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_7, prime_nineteenQ_317, prime_nineteenQ_26713663, prime_nineteenQ_94736729819765531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870429 : Nat.totient 22463070797953623082715870429 = 21647000232688610344169041920 := by
  rw [← show ((([(29, 1), (523, 1), (1725697, 1), (858232378305983971, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_29, prime_nineteenQ_523, prime_nineteenQ_1725697, prime_nineteenQ_858232378305983971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870430 : Nat.totient 22463070797953623082715870430 = 5990082565273413108122096256 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (86183, 1), (42041059, 1), (206658187604573, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_86183, prime_nineteenQ_42041059, prime_nineteenQ_206658187604573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870431 : Nat.totient 22463070797953623082715870431 = 21738455610922861047789552000 := by
  rw [← show ((([(31, 1), (724615187030762034926318401, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_31, prime_nineteenQ_724615187030762034926318401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870432 : Nat.totient 22463070797953623082715870432 = 11231523153823563727603614720 := by
  rw [← show ((([(2, 5), (1318411, 1), (3014237, 1), (176640763490393, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_1318411, prime_nineteenQ_3014237, prime_nineteenQ_176640763490393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870433 : Nat.totient 22463070797953623082715870433 = 13613982301790074595585376000 := by
  rw [← show ((([(3, 1), (11, 1), (680699115089503729779268801, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_11, prime_nineteenQ_680699115089503729779268801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870434 : Nat.totient 22463070797953623082715870434 = 10556892701892797215805337600 := by
  rw [← show ((([(2, 1), (17, 1), (757, 1), (25340904301, 1), (34440719883793, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_17, prime_nineteenQ_757, prime_nineteenQ_25340904301, prime_nineteenQ_34440719883793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870435 : Nat.totient 22463070797953623082715870435 = 15384623095478757090750003168 := by
  rw [← show ((([(5, 1), (7, 1), (827, 1), (776060487060066439202483, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_7, prime_nineteenQ_827, prime_nineteenQ_776060487060066439202483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870436 : Nat.totient 22463070797953623082715870436 = 7487690260385148275543087424 := by
  rw [← show ((([(2, 2), (3, 2), (1337232557, 1), (466616061331839893, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_1337232557, prime_nineteenQ_466616061331839893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870437 : Nat.totient 22463070797953623082715870437 = 21793423368251338655247273600 := by
  rw [← show ((([(37, 1), (359, 1), (13151, 1), (128592066474141292489, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_37, prime_nineteenQ_359, prime_nineteenQ_13151, prime_nineteenQ_128592066474141292489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870438 : Nat.totient 22463070797953623082715870438 = 10640401948222420416879709800 := by
  rw [← show ((([(2, 1), (19, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_19, prime_nineteenQ_1222615931, prime_nineteenQ_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870439 : Nat.totient 22463070797953623082715870439 = 13584255337555953387688251648 := by
  rw [← show ((([(3, 1), (13, 1), (89, 1), (163, 1), (39703327656062808021443, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_13, prime_nineteenQ_89, prime_nineteenQ_163, prime_nineteenQ_39703327656062808021443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870440 : Nat.totient 22463070797953623082715870440 = 8933290583232423514976019712 := by
  rw [← show ((([(2, 3), (5, 1), (173, 1), (3246108496814107381895357, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_5, prime_nineteenQ_173, prime_nineteenQ_3246108496814107381895357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870441 : Nat.totient 22463070797953623082715870441 = 21657223904570903426991083520 := by
  rw [← show ((([(41, 1), (97, 1), (677, 1), (8343050382369831510029, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_41, prime_nineteenQ_97, prime_nineteenQ_677, prime_nineteenQ_8343050382369831510029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870442 : Nat.totient 22463070797953623082715870442 = 6418020114353641247290957824 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (59767193, 1), (1189299689, 1), (7524292513, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_7, prime_nineteenQ_59767193, prime_nineteenQ_1189299689, prime_nineteenQ_7524292513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870443 : Nat.totient 22463070797953623082715870443 = 21940338414489889543099713504 := by
  rw [← show ((([(43, 1), (65419, 1), (17671339223, 1), (451884354773, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_43, prime_nineteenQ_65419, prime_nineteenQ_17671339223, prime_nineteenQ_451884354773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870444 : Nat.totient 22463070797953623082715870444 = 10209884313537634460494060800 := by
  rw [← show ((([(2, 2), (11, 1), (17419, 1), (628561, 1), (46627893857328739, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_11, prime_nineteenQ_17419, prime_nineteenQ_628561, prime_nineteenQ_46627893857328739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870445 : Nat.totient 22463070797953623082715870445 = 11980300312718167463829880800 := by
  rw [← show ((([(3, 2), (5, 1), (2912891, 1), (171369045757508972531, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_2912891, prime_nineteenQ_171369045757508972531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870446 : Nat.totient 22463070797953623082715870446 = 10742688300368818995557104320 := by
  rw [← show ((([(2, 1), (23, 1), (20681, 1), (58384288267, 1), (404430377963, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_23, prime_nineteenQ_20681, prime_nineteenQ_58384288267, prime_nineteenQ_404430377963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870447 : Nat.totient 22463070797953623082715870447 = 21437890379779514011923087360 := by
  rw [← show ((([(47, 1), (83, 1), (179, 1), (229, 1), (353, 1), (3709, 1), (107293428600521, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_47, prime_nineteenQ_83, prime_nineteenQ_179, prime_nineteenQ_229, prime_nineteenQ_353, prime_nineteenQ_3709, prime_nineteenQ_107293428600521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870448 : Nat.totient 22463070797953623082715870448 = 7487690256524439113210767872 := by
  rw [← show ((([(2, 4), (3, 1), (791502073, 1), (591256368856072237, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_791502073, prime_nineteenQ_591256368856072237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870449 : Nat.totient 22463070797953623082715870449 = 19241059967765811997156003200 := by
  rw [← show ((([(7, 2), (1481, 1), (309540861772294272798521, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_7, prime_nineteenQ_1481, prime_nineteenQ_309540861772294272798521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870450 : Nat.totient 22463070797953623082715870450 = 8985111233176399963147513920 := by
  rw [← show ((([(2, 1), (5, 2), (77587, 1), (7032919, 1), (823331149041853, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_5, prime_nineteenQ_77587, prime_nineteenQ_7032919, prime_nineteenQ_823331149041853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870451 : Nat.totient 22463070797953623082715870451 = 14061219606915158571828956160 := by
  rw [← show ((([(3, 1), (17, 1), (479, 1), (3671, 1), (250483458960529628089, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_17, prime_nineteenQ_479, prime_nineteenQ_3671, prime_nineteenQ_250483458960529628089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870452 : Nat.totient 22463070797953623082715870452 = 10139357663535418597859323392 := by
  rw [← show ((([(2, 2), (13, 1), (67, 1), (139, 1), (46384852435292319013777, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_13, prime_nineteenQ_67, prime_nineteenQ_139, prime_nineteenQ_46384852435292319013777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870453 : Nat.totient 22463070797953623082715870453 = 22039233924742565833386826560 := by
  rw [← show ((([(53, 1), (4145299, 1), (691107271, 1), (147942152269, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_53, prime_nineteenQ_4145299, prime_nineteenQ_691107271, prime_nineteenQ_147942152269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870454 : Nat.totient 22463070797953623082715870454 = 7487597794825709021951642880 := by
  rw [← show ((([(2, 1), (3, 4), (101383, 1), (402221, 1), (3400354777907569, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_101383, prime_nineteenQ_402221, prime_nineteenQ_3400354777907569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870455 : Nat.totient 22463070797953623082715870455 = 16332908898882089304179598720 := by
  rw [← show ((([(5, 1), (11, 1), (4229, 1), (2392267, 1), (40370032756168967, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_11, prime_nineteenQ_4229, prime_nineteenQ_2392267, prime_nineteenQ_40370032756168967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870456 : Nat.totient 22463070797953623082715870456 = 9491438365332516795513746400 := by
  rw [← show ((([(2, 3), (7, 1), (71, 1), (5649665693650307616377231, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_7, prime_nineteenQ_71, prime_nineteenQ_5649665693650307616377231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870457 : Nat.totient 22463070797953623082715870457 = 14187202609233867210136339200 := by
  rw [← show ((([(3, 1), (19, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_19, prime_nineteenQ_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870458 : Nat.totient 22463070797953623082715870458 = 10819221602394775236692433408 := by
  rw [← show ((([(2, 1), (29, 2), (617, 1), (1459, 1), (468157, 1), (31689191359339, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_29, prime_nineteenQ_617, prime_nineteenQ_1459, prime_nineteenQ_468157, prime_nineteenQ_31689191359339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870459 : Nat.totient 22463070797953623082715870459 = 21996106344521750335932437760 := by
  rw [← show ((([(59, 1), (269, 1), (5309, 1), (266595066891837371881, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_59, prime_nineteenQ_269, prime_nineteenQ_5309, prime_nineteenQ_266595066891837371881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870460 : Nat.totient 22463070797953623082715870460 = 5990152212787632822057565440 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (374384513299227051378597841, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_374384513299227051378597841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870461 : Nat.totient 22463070797953623082715870461 = 22094823735692088278081184000 := by
  rw [← show ((([(61, 1), (368247062261534804634686401, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_61, prime_nineteenQ_368247062261534804634686401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870462 : Nat.totient 22463070797953623082715870462 = 10869223990060012490235423360 := by
  rw [← show ((([(2, 1), (31, 1), (2848777, 1), (127180047267785796313, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_31, prime_nineteenQ_2848777, prime_nineteenQ_127180047267785796313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870463 : Nat.totient 22463070797953623082715870463 = 12836040455970371459038502592 := by
  rw [← show ((([(3, 2), (7, 1), (4319049457733, 1), (82554433057997, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_7, prime_nineteenQ_4319049457733, prime_nineteenQ_82554433057997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870464 : Nat.totient 22463070797953623082715870464 = 11231535398883826161931773440 := by
  rw [← show ((([(2, 8), (120808277411, 1), (726327468489479, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_120808277411, prime_nineteenQ_726327468489479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870465 : Nat.totient 22463070797953623082715870465 = 16588113820027290891851719680 := by
  rw [← show ((([(5, 1), (13, 1), (345585704583901893580244161, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_13, prime_nineteenQ_345585704583901893580244161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870466 : Nat.totient 22463070797953623082715870466 = 6709028316752151235722240000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (79, 1), (631, 1), (5849, 1), (82208521, 1), (14199409481, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_11, prime_nineteenQ_79, prime_nineteenQ_631, prime_nineteenQ_5849, prime_nineteenQ_82208521, prime_nineteenQ_14199409481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870467 : Nat.totient 22463070797953623082715870467 = 22462831775716762149708586416 := by
  rw [← show ((([(93979, 1), (239022236860933007190073, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_93979, prime_nineteenQ_239022236860933007190073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870468 : Nat.totient 22463070797953623082715870468 = 10570856685197896137519779328 := by
  rw [← show ((([(2, 2), (17, 1), (65699149, 1), (5028060202735570549, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_17, prime_nineteenQ_65699149, prime_nineteenQ_5028060202735570549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870469 : Nat.totient 22463070797953623082715870469 = 14315088911893695973508947376 := by
  rw [← show ((([(3, 1), (23, 1), (1559, 1), (208820879214227097291239, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_23, prime_nineteenQ_1559, prime_nineteenQ_208820879214227097291239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870470 : Nat.totient 22463070797953623082715870470 = 7627106058953314980785356800 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (131, 1), (503, 1), (14321, 1), (111343009, 1), (3054186173, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_5, prime_nineteenQ_7, prime_nineteenQ_131, prime_nineteenQ_503, prime_nineteenQ_14321, prime_nineteenQ_111343009, prime_nineteenQ_3054186173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870471 : Nat.totient 22463070797953623082715870471 = 22463070797953623082715870470 := by
  rw [← show ((([(22463070797953623082715870471, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_22463070797953623082715870471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870472 : Nat.totient 22463070797953623082715870472 = 7486048588662465925395225600 := by
  rw [← show ((([(2, 3), (3, 2), (4561, 1), (68403221753129257359241, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_4561, prime_nineteenQ_68403221753129257359241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870473 : Nat.totient 22463070797953623082715870473 = 22462981748186928717839550480 := by
  rw [← show ((([(252253, 1), (89049766694364876067741, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_252253, prime_nineteenQ_89049766694364876067741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870474 : Nat.totient 22463070797953623082715870474 = 10927980388193654472672585600 := by
  rw [← show ((([(2, 1), (37, 1), (303555010783157068685349601, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_37, prime_nineteenQ_303555010783157068685349601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870475 : Nat.totient 22463070797953623082715870475 = 11900964661052219714030688000 := by
  rw [← show ((([(3, 1), (5, 2), (151, 1), (103811766649, 1), (19106640549727, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_151, prime_nineteenQ_103811766649, prime_nineteenQ_19106640549727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870476 : Nat.totient 22463070797953623082715870476 = 10640401448562892343926720512 := by
  rw [← show ((([(2, 2), (19, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_19, prime_nineteenQ_20930737, prime_nineteenQ_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870477 : Nat.totient 22463070797953623082715870477 = 17406986052801831763889736000 := by
  rw [← show ((([(7, 1), (11, 1), (181, 1), (1611757967852021459619421, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_7, prime_nineteenQ_11, prime_nineteenQ_181, prime_nineteenQ_1611757967852021459619421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870478 : Nat.totient 22463070797953623082715870478 = 6911701662635254194555341952 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (587527, 1), (10394107, 1), (47158448706709, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_13, prime_nineteenQ_587527, prime_nineteenQ_10394107, prime_nineteenQ_47158448706709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870479 : Nat.totient 22463070797953623082715870479 = 22413846545736034492694268864 := by
  rw [← show ((([(457, 1), (622067, 1), (642359, 1), (123009300652699, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_457, prime_nineteenQ_622067, prime_nineteenQ_642359, prime_nineteenQ_123009300652699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870480 : Nat.totient 22463070797953623082715870480 = 8976420544954789812116275200 := by
  rw [← show ((([(2, 4), (5, 1), (1021, 1), (1227929, 1), (264938021, 1), (845348629, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_5, prime_nineteenQ_1021, prime_nineteenQ_1227929, prime_nineteenQ_264938021, prime_nineteenQ_845348629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870481 : Nat.totient 22463070797953623082715870481 = 14975380249638716260254355344 := by
  rw [← show ((([(3, 3), (53042047, 1), (15685020321885266749, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_53042047, prime_nineteenQ_15685020321885266749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870482 : Nat.totient 22463070797953623082715870482 = 10957595511160900499054174080 := by
  rw [← show ((([(2, 1), (41, 1), (304575402293, 1), (899415664290557, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_41, prime_nineteenQ_304575402293, prime_nineteenQ_899415664290557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870483 : Nat.totient 22463070797953623082715870483 = 22460024281142938339872838080 := by
  rw [← show ((([(9433, 1), (64171, 1), (71263, 1), (520734537703487, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_9433, prime_nineteenQ_64171, prime_nineteenQ_71263, prime_nineteenQ_520734537703487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870484 : Nat.totient 22463070797953623082715870484 = 6417929035724455490233334496 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (70379, 1), (3799677595581748729619, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_7, prime_nineteenQ_70379, prime_nineteenQ_3799677595581748729619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870485 : Nat.totient 22463070797953623082715870485 = 16868285407208393170321670144 := by
  rw [← show ((([(5, 1), (17, 1), (509, 1), (1499, 2), (32573, 1), (217409, 1), (32628257, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_17, prime_nineteenQ_509, prime_nineteenQ_1499, prime_nineteenQ_32573, prime_nineteenQ_217409, prime_nineteenQ_32628257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870486 : Nat.totient 22463070797953623082715870486 = 10970336900781162323161311744 := by
  rw [← show ((([(2, 1), (43, 1), (20128140817, 1), (12976782109454353, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_43, prime_nineteenQ_20128140817, prime_nineteenQ_12976782109454353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870487 : Nat.totient 22463070797953623082715870487 = 14450698091736857680446243072 := by
  rw [← show ((([(3, 1), (29, 1), (1753, 1), (345143, 1), (426745438376754719, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_29, prime_nineteenQ_1753, prime_nineteenQ_345143, prime_nineteenQ_426745438376754719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870488 : Nat.totient 22463070797953623082715870488 = 10210149957757630897842320160 := by
  rw [← show ((([(2, 3), (11, 1), (30319, 1), (8419214623126221137479, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_11, prime_nineteenQ_30319, prime_nineteenQ_8419214623126221137479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870489 : Nat.totient 22463070797953623082715870489 = 22240663590679147875422372400 := by
  rw [← show ((([(101, 1), (39314563, 1), (5657105779451173303, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_101, prime_nineteenQ_39314563, prime_nineteenQ_5657105779451173303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870490 : Nat.totient 22463070797953623082715870490 = 5980835276159313344592545280 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (863, 1), (3359, 1), (10067, 1), (13685389, 1), (624954791, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_5, prime_nineteenQ_863, prime_nineteenQ_3359, prime_nineteenQ_10067, prime_nineteenQ_13685389, prime_nineteenQ_624954791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870491 : Nat.totient 22463070797953623082715870491 = 17772889676347781002280848896 := by
  rw [← show ((([(7, 1), (13, 1), (198769, 1), (16925396167, 1), (73373669287, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_7, prime_nineteenQ_13, prime_nineteenQ_198769, prime_nineteenQ_16925396167, prime_nineteenQ_73373669287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870492 : Nat.totient 22463070797953623082715870492 = 10737556427446211889137480000 := by
  rw [← show ((([(2, 2), (23, 1), (1901, 1), (128439670184763300109301, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_23, prime_nineteenQ_1901, prime_nineteenQ_128439670184763300109301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870493 : Nat.totient 22463070797953623082715870493 = 14492090765898847855598155200 := by
  rw [← show ((([(3, 1), (31, 1), (68059, 1), (387951181, 1), (9147944801119, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_31, prime_nineteenQ_68059, prime_nineteenQ_387951181, prime_nineteenQ_9147944801119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870494 : Nat.totient 22463070797953623082715870494 = 10992566560627423269052329600 := by
  rw [← show ((([(2, 1), (47, 1), (150009781321, 1), (1593021709462681, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_47, prime_nineteenQ_150009781321, prime_nineteenQ_1593021709462681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870495 : Nat.totient 22463070797953623082715870495 = 17024643103888229972830534944 := by
  rw [← show ((([(5, 1), (19, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_5, prime_nineteenQ_19, prime_nineteenQ_626080687, prime_nineteenQ_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870496 : Nat.totient 22463070797953623082715870496 = 7487690265984541027571956800 := by
  rw [← show ((([(2, 5), (3, 1), (233990320812016907111623651, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_3, prime_nineteenQ_233990320812016907111623651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870497 : Nat.totient 22463070797953623082715870497 = 22460802029908288857870998400 := by
  rw [← show ((([(9901, 1), (138529476269, 1), (16377509992313, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_9901, prime_nineteenQ_138529476269, prime_nineteenQ_16377509992313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870498 : Nat.totient 22463070797953623082715870498 = 9612287569634059669611051744 := by
  rw [← show ((([(2, 1), (7, 2), (653, 1), (351018389192012111802917, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_2, prime_nineteenQ_7, prime_nineteenQ_653, prime_nineteenQ_351018389192012111802917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nineteenQ_22463070797953623082715870499 : Nat.totient 22463070797953623082715870499 = 13427487696045783764548177920 := by
  rw [← show ((([(3, 2), (11, 1), (73, 1), (7910153, 1), (392939951653905329, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953623082715870499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nineteenQ_3, prime_nineteenQ_11, prime_nineteenQ_73, prime_nineteenQ_7910153, prime_nineteenQ_392939951653905329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NineteenQ : certifiedKill 1 22463070797953623082715870399 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_nineteenQ_22463070797953623082715870400, phi_nineteenQ_22463070797953623082715870401, phi_nineteenQ_22463070797953623082715870402,
    phi_nineteenQ_22463070797953623082715870403, phi_nineteenQ_22463070797953623082715870404, phi_nineteenQ_22463070797953623082715870405,
    phi_nineteenQ_22463070797953623082715870406, phi_nineteenQ_22463070797953623082715870407, phi_nineteenQ_22463070797953623082715870408,
    phi_nineteenQ_22463070797953623082715870409, phi_nineteenQ_22463070797953623082715870410, phi_nineteenQ_22463070797953623082715870411,
    phi_nineteenQ_22463070797953623082715870412, phi_nineteenQ_22463070797953623082715870413, phi_nineteenQ_22463070797953623082715870414,
    phi_nineteenQ_22463070797953623082715870415, phi_nineteenQ_22463070797953623082715870416, phi_nineteenQ_22463070797953623082715870417,
    phi_nineteenQ_22463070797953623082715870418, phi_nineteenQ_22463070797953623082715870419, phi_nineteenQ_22463070797953623082715870420,
    phi_nineteenQ_22463070797953623082715870421, phi_nineteenQ_22463070797953623082715870422, phi_nineteenQ_22463070797953623082715870423,
    phi_nineteenQ_22463070797953623082715870424, phi_nineteenQ_22463070797953623082715870425, phi_nineteenQ_22463070797953623082715870426,
    phi_nineteenQ_22463070797953623082715870427, phi_nineteenQ_22463070797953623082715870428, phi_nineteenQ_22463070797953623082715870429,
    phi_nineteenQ_22463070797953623082715870430, phi_nineteenQ_22463070797953623082715870431, phi_nineteenQ_22463070797953623082715870432,
    phi_nineteenQ_22463070797953623082715870433, phi_nineteenQ_22463070797953623082715870434, phi_nineteenQ_22463070797953623082715870435,
    phi_nineteenQ_22463070797953623082715870436, phi_nineteenQ_22463070797953623082715870437, phi_nineteenQ_22463070797953623082715870438,
    phi_nineteenQ_22463070797953623082715870439, phi_nineteenQ_22463070797953623082715870440, phi_nineteenQ_22463070797953623082715870441,
    phi_nineteenQ_22463070797953623082715870442, phi_nineteenQ_22463070797953623082715870443, phi_nineteenQ_22463070797953623082715870444,
    phi_nineteenQ_22463070797953623082715870445, phi_nineteenQ_22463070797953623082715870446, phi_nineteenQ_22463070797953623082715870447,
    phi_nineteenQ_22463070797953623082715870448, phi_nineteenQ_22463070797953623082715870449, phi_nineteenQ_22463070797953623082715870450,
    phi_nineteenQ_22463070797953623082715870451, phi_nineteenQ_22463070797953623082715870452, phi_nineteenQ_22463070797953623082715870453,
    phi_nineteenQ_22463070797953623082715870454, phi_nineteenQ_22463070797953623082715870455, phi_nineteenQ_22463070797953623082715870456,
    phi_nineteenQ_22463070797953623082715870457, phi_nineteenQ_22463070797953623082715870458, phi_nineteenQ_22463070797953623082715870459,
    phi_nineteenQ_22463070797953623082715870460, phi_nineteenQ_22463070797953623082715870461, phi_nineteenQ_22463070797953623082715870462,
    phi_nineteenQ_22463070797953623082715870463, phi_nineteenQ_22463070797953623082715870464, phi_nineteenQ_22463070797953623082715870465,
    phi_nineteenQ_22463070797953623082715870466, phi_nineteenQ_22463070797953623082715870467, phi_nineteenQ_22463070797953623082715870468,
    phi_nineteenQ_22463070797953623082715870469, phi_nineteenQ_22463070797953623082715870470, phi_nineteenQ_22463070797953623082715870471,
    phi_nineteenQ_22463070797953623082715870472, phi_nineteenQ_22463070797953623082715870473, phi_nineteenQ_22463070797953623082715870474,
    phi_nineteenQ_22463070797953623082715870475, phi_nineteenQ_22463070797953623082715870476, phi_nineteenQ_22463070797953623082715870477,
    phi_nineteenQ_22463070797953623082715870478, phi_nineteenQ_22463070797953623082715870479, phi_nineteenQ_22463070797953623082715870480,
    phi_nineteenQ_22463070797953623082715870481, phi_nineteenQ_22463070797953623082715870482, phi_nineteenQ_22463070797953623082715870483,
    phi_nineteenQ_22463070797953623082715870484, phi_nineteenQ_22463070797953623082715870485, phi_nineteenQ_22463070797953623082715870486,
    phi_nineteenQ_22463070797953623082715870487, phi_nineteenQ_22463070797953623082715870488, phi_nineteenQ_22463070797953623082715870489,
    phi_nineteenQ_22463070797953623082715870490, phi_nineteenQ_22463070797953623082715870491, phi_nineteenQ_22463070797953623082715870492,
    phi_nineteenQ_22463070797953623082715870493, phi_nineteenQ_22463070797953623082715870494, phi_nineteenQ_22463070797953623082715870495,
    phi_nineteenQ_22463070797953623082715870496, phi_nineteenQ_22463070797953623082715870497, phi_nineteenQ_22463070797953623082715870498,
    phi_nineteenQ_22463070797953623082715870499]

end TotientTailPeriodKiller
end Erdos249257
