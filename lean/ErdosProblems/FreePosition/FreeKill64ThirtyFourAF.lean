import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtyFourAFFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyFourAFFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyFourAFFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyFourAFFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyFourAFFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyFourAFFastPow a n * thirtyFourAFFastPow a n * a
        else thirtyFourAFFastPow a n * thirtyFourAFFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyFourAF_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtyFourAF_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtyFourAF_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtyFourAF_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtyFourAF_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtyFourAF_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtyFourAF_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtyFourAF_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtyFourAF_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtyFourAF_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtyFourAF_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtyFourAF_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtyFourAF_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtyFourAF_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtyFourAF_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtyFourAF_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtyFourAF_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtyFourAF_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtyFourAF_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtyFourAF_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtyFourAF_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtyFourAF_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtyFourAF_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtyFourAF_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtyFourAF_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtyFourAF_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtyFourAF_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtyFourAF_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtyFourAF_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtyFourAF_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtyFourAF_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtyFourAF_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtyFourAF_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtyFourAF_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtyFourAF_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtyFourAF_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtyFourAF_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtyFourAF_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtyFourAF_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirtyFourAF_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtyFourAF_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtyFourAF_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtyFourAF_197 : Nat.Prime 197 := by norm_num
private theorem prime_thirtyFourAF_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtyFourAF_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtyFourAF_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtyFourAF_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtyFourAF_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtyFourAF_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirtyFourAF_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtyFourAF_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtyFourAF_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtyFourAF_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtyFourAF_263 : Nat.Prime 263 := by norm_num
private theorem prime_thirtyFourAF_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtyFourAF_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirtyFourAF_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtyFourAF_283 : Nat.Prime 283 := by norm_num
private theorem prime_thirtyFourAF_293 : Nat.Prime 293 := by norm_num
private theorem prime_thirtyFourAF_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirtyFourAF_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtyFourAF_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtyFourAF_337 : Nat.Prime 337 := by norm_num
private theorem prime_thirtyFourAF_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtyFourAF_349 : Nat.Prime 349 := by norm_num
private theorem prime_thirtyFourAF_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirtyFourAF_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtyFourAF_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirtyFourAF_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtyFourAF_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtyFourAF_419 : Nat.Prime 419 := by norm_num
private theorem prime_thirtyFourAF_421 : Nat.Prime 421 := by norm_num
private theorem prime_thirtyFourAF_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtyFourAF_439 : Nat.Prime 439 := by norm_num
private theorem prime_thirtyFourAF_443 : Nat.Prime 443 := by norm_num
private theorem prime_thirtyFourAF_449 : Nat.Prime 449 := by norm_num
private theorem prime_thirtyFourAF_461 : Nat.Prime 461 := by norm_num
private theorem prime_thirtyFourAF_463 : Nat.Prime 463 := by norm_num
private theorem prime_thirtyFourAF_467 : Nat.Prime 467 := by norm_num
private theorem prime_thirtyFourAF_479 : Nat.Prime 479 := by norm_num
private theorem prime_thirtyFourAF_487 : Nat.Prime 487 := by norm_num
private theorem prime_thirtyFourAF_491 : Nat.Prime 491 := by norm_num
private theorem prime_thirtyFourAF_521 : Nat.Prime 521 := by norm_num
private theorem prime_thirtyFourAF_541 : Nat.Prime 541 := by norm_num
private theorem prime_thirtyFourAF_571 : Nat.Prime 571 := by norm_num
private theorem prime_thirtyFourAF_599 : Nat.Prime 599 := by norm_num
private theorem prime_thirtyFourAF_601 : Nat.Prime 601 := by norm_num
private theorem prime_thirtyFourAF_607 : Nat.Prime 607 := by norm_num
private theorem prime_thirtyFourAF_631 : Nat.Prime 631 := by norm_num
private theorem prime_thirtyFourAF_641 : Nat.Prime 641 := by norm_num
private theorem prime_thirtyFourAF_647 : Nat.Prime 647 := by norm_num
private theorem prime_thirtyFourAF_653 : Nat.Prime 653 := by norm_num
private theorem prime_thirtyFourAF_659 : Nat.Prime 659 := by norm_num
private theorem prime_thirtyFourAF_661 : Nat.Prime 661 := by norm_num
private theorem prime_thirtyFourAF_677 : Nat.Prime 677 := by norm_num
private theorem prime_thirtyFourAF_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtyFourAF_739 : Nat.Prime 739 := by norm_num
private theorem prime_thirtyFourAF_743 : Nat.Prime 743 := by norm_num
private theorem prime_thirtyFourAF_757 : Nat.Prime 757 := by norm_num
private theorem prime_thirtyFourAF_773 : Nat.Prime 773 := by norm_num
private theorem prime_thirtyFourAF_809 : Nat.Prime 809 := by norm_num
private theorem prime_thirtyFourAF_811 : Nat.Prime 811 := by norm_num
private theorem prime_thirtyFourAF_821 : Nat.Prime 821 := by norm_num
private theorem prime_thirtyFourAF_829 : Nat.Prime 829 := by norm_num
private theorem prime_thirtyFourAF_853 : Nat.Prime 853 := by norm_num
private theorem prime_thirtyFourAF_887 : Nat.Prime 887 := by norm_num
private theorem prime_thirtyFourAF_947 : Nat.Prime 947 := by norm_num
private theorem prime_thirtyFourAF_971 : Nat.Prime 971 := by norm_num
private theorem prime_thirtyFourAF_983 : Nat.Prime 983 := by norm_num
private theorem prime_thirtyFourAF_997 : Nat.Prime 997 := by norm_num
private theorem prime_thirtyFourAF_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_thirtyFourAF_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_thirtyFourAF_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_thirtyFourAF_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_thirtyFourAF_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_thirtyFourAF_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_thirtyFourAF_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_thirtyFourAF_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_thirtyFourAF_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_thirtyFourAF_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_thirtyFourAF_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_thirtyFourAF_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_thirtyFourAF_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_thirtyFourAF_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_thirtyFourAF_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_thirtyFourAF_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_thirtyFourAF_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_thirtyFourAF_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_thirtyFourAF_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_thirtyFourAF_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_thirtyFourAF_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_thirtyFourAF_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_thirtyFourAF_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_thirtyFourAF_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_thirtyFourAF_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_thirtyFourAF_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_thirtyFourAF_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_thirtyFourAF_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_thirtyFourAF_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_thirtyFourAF_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_thirtyFourAF_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_thirtyFourAF_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_thirtyFourAF_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_thirtyFourAF_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_thirtyFourAF_2459 : Nat.Prime 2459 := by norm_num
private theorem prime_thirtyFourAF_2503 : Nat.Prime 2503 := by norm_num
private theorem prime_thirtyFourAF_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtyFourAF_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_thirtyFourAF_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_thirtyFourAF_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_thirtyFourAF_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_thirtyFourAF_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_thirtyFourAF_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_thirtyFourAF_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_thirtyFourAF_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_thirtyFourAF_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_thirtyFourAF_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_thirtyFourAF_3259 : Nat.Prime 3259 := by norm_num
private theorem prime_thirtyFourAF_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_thirtyFourAF_3407 : Nat.Prime 3407 := by norm_num
private theorem prime_thirtyFourAF_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_thirtyFourAF_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_thirtyFourAF_3637 : Nat.Prime 3637 := by norm_num
private theorem prime_thirtyFourAF_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_thirtyFourAF_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_thirtyFourAF_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_thirtyFourAF_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_thirtyFourAF_3863 : Nat.Prime 3863 := by norm_num
private theorem prime_thirtyFourAF_3917 : Nat.Prime 3917 := by norm_num
private theorem prime_thirtyFourAF_3929 : Nat.Prime 3929 := by norm_num
private theorem prime_thirtyFourAF_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_thirtyFourAF_4271 : Nat.Prime 4271 := by norm_num
private theorem prime_thirtyFourAF_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_thirtyFourAF_4423 : Nat.Prime 4423 := by norm_num
private theorem prime_thirtyFourAF_4801 : Nat.Prime 4801 := by norm_num
private theorem prime_thirtyFourAF_4943 : Nat.Prime 4943 := by norm_num
private theorem prime_thirtyFourAF_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtyFourAF_5281 : Nat.Prime 5281 := by norm_num
private theorem prime_thirtyFourAF_5387 : Nat.Prime 5387 := by norm_num
private theorem prime_thirtyFourAF_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_thirtyFourAF_5653 : Nat.Prime 5653 := by norm_num
private theorem prime_thirtyFourAF_5657 : Nat.Prime 5657 := by norm_num
private theorem prime_thirtyFourAF_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_thirtyFourAF_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_thirtyFourAF_5839 : Nat.Prime 5839 := by norm_num
private theorem prime_thirtyFourAF_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_thirtyFourAF_6101 : Nat.Prime 6101 := by norm_num
private theorem prime_thirtyFourAF_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_thirtyFourAF_6337 : Nat.Prime 6337 := by norm_num
private theorem prime_thirtyFourAF_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_thirtyFourAF_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_thirtyFourAF_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_thirtyFourAF_6679 : Nat.Prime 6679 := by norm_num
private theorem prime_thirtyFourAF_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtyFourAF_6827 : Nat.Prime 6827 := by norm_num
private theorem prime_thirtyFourAF_6971 : Nat.Prime 6971 := by norm_num
private theorem prime_thirtyFourAF_7187 : Nat.Prime 7187 := by norm_num
private theorem prime_thirtyFourAF_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_thirtyFourAF_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_thirtyFourAF_7529 : Nat.Prime 7529 := by norm_num
private theorem prime_thirtyFourAF_8039 : Nat.Prime 8039 := by norm_num
private theorem prime_thirtyFourAF_8087 : Nat.Prime 8087 := by norm_num
private theorem prime_thirtyFourAF_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_thirtyFourAF_8893 : Nat.Prime 8893 := by norm_num
private theorem prime_thirtyFourAF_8929 : Nat.Prime 8929 := by norm_num
private theorem prime_thirtyFourAF_9013 : Nat.Prime 9013 := by norm_num
private theorem prime_thirtyFourAF_9743 : Nat.Prime 9743 := by norm_num
private theorem prime_thirtyFourAF_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_thirtyFourAF_10037 : Nat.Prime 10037 := by norm_num
private theorem prime_thirtyFourAF_10211 : Nat.Prime 10211 := by norm_num
private theorem prime_thirtyFourAF_11197 : Nat.Prime 11197 := by norm_num
private theorem prime_thirtyFourAF_11317 : Nat.Prime 11317 := by norm_num
private theorem prime_thirtyFourAF_11833 : Nat.Prime 11833 := by norm_num
private theorem prime_thirtyFourAF_12973 : Nat.Prime 12973 := by norm_num
private theorem prime_thirtyFourAF_13757 : Nat.Prime 13757 := by norm_num
private theorem prime_thirtyFourAF_14593 : Nat.Prime 14593 := by norm_num
private theorem prime_thirtyFourAF_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_thirtyFourAF_15541 : Nat.Prime 15541 := by norm_num
private theorem prime_thirtyFourAF_15727 : Nat.Prime 15727 := by norm_num
private theorem prime_thirtyFourAF_15749 : Nat.Prime 15749 := by norm_num
private theorem prime_thirtyFourAF_16111 : Nat.Prime 16111 := by norm_num
private theorem prime_thirtyFourAF_17021 : Nat.Prime 17021 := by norm_num
private theorem prime_thirtyFourAF_19421 : Nat.Prime 19421 := by norm_num
private theorem prime_thirtyFourAF_19891 : Nat.Prime 19891 := by norm_num
private theorem prime_thirtyFourAF_20431 : Nat.Prime 20431 := by norm_num
private theorem prime_thirtyFourAF_21997 : Nat.Prime 21997 := by norm_num
private theorem prime_thirtyFourAF_22409 : Nat.Prime 22409 := by norm_num
private theorem prime_thirtyFourAF_22717 : Nat.Prime 22717 := by norm_num
private theorem prime_thirtyFourAF_24281 : Nat.Prime 24281 := by norm_num
private theorem prime_thirtyFourAF_24469 : Nat.Prime 24469 := by norm_num
private theorem prime_thirtyFourAF_24847 : Nat.Prime 24847 := by norm_num
private theorem prime_thirtyFourAF_24923 : Nat.Prime 24923 := by norm_num
private theorem prime_thirtyFourAF_25127 : Nat.Prime 25127 := by norm_num
private theorem prime_thirtyFourAF_25693 : Nat.Prime 25693 := by norm_num
private theorem prime_thirtyFourAF_26227 : Nat.Prime 26227 := by norm_num
private theorem prime_thirtyFourAF_28493 : Nat.Prime 28493 := by norm_num
private theorem prime_thirtyFourAF_28547 : Nat.Prime 28547 := by norm_num
private theorem prime_thirtyFourAF_29641 : Nat.Prime 29641 := by norm_num
private theorem prime_thirtyFourAF_30931 : Nat.Prime 30931 := by norm_num
private theorem prime_thirtyFourAF_31319 : Nat.Prime 31319 := by norm_num
private theorem prime_thirtyFourAF_32359 : Nat.Prime 32359 := by norm_num
private theorem prime_thirtyFourAF_33479 : Nat.Prime 33479 := by norm_num
private theorem prime_thirtyFourAF_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtyFourAF_36923 : Nat.Prime 36923 := by norm_num
private theorem prime_thirtyFourAF_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtyFourAF_37847 : Nat.Prime 37847 := by norm_num
private theorem prime_thirtyFourAF_40163 : Nat.Prime 40163 := by norm_num
private theorem prime_thirtyFourAF_41983 : Nat.Prime 41983 := by norm_num
private theorem prime_thirtyFourAF_42737 : Nat.Prime 42737 := by norm_num
private theorem prime_thirtyFourAF_45263 : Nat.Prime 45263 := by norm_num
private theorem prime_thirtyFourAF_46133 : Nat.Prime 46133 := by norm_num
private theorem prime_thirtyFourAF_47129 : Nat.Prime 47129 := by norm_num
private theorem prime_thirtyFourAF_49279 : Nat.Prime 49279 := by norm_num
private theorem prime_thirtyFourAF_49417 : Nat.Prime 49417 := by norm_num
private theorem prime_thirtyFourAF_53407 : Nat.Prime 53407 := by norm_num
private theorem prime_thirtyFourAF_54601 : Nat.Prime 54601 := by norm_num
private theorem prime_thirtyFourAF_54833 : Nat.Prime 54833 := by norm_num
private theorem prime_thirtyFourAF_57641 : Nat.Prime 57641 := by norm_num
private theorem prime_thirtyFourAF_59581 : Nat.Prime 59581 := by norm_num
private theorem prime_thirtyFourAF_60887 : Nat.Prime 60887 := by norm_num
private theorem prime_thirtyFourAF_61007 : Nat.Prime 61007 := by norm_num
private theorem prime_thirtyFourAF_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtyFourAF_68927 : Nat.Prime 68927 := by norm_num
private theorem prime_thirtyFourAF_76679 : Nat.Prime 76679 := by norm_num
private theorem prime_thirtyFourAF_81971 : Nat.Prime 81971 := by norm_num
private theorem prime_thirtyFourAF_82139 : Nat.Prime 82139 := by norm_num
private theorem prime_thirtyFourAF_83047 : Nat.Prime 83047 := by norm_num
private theorem prime_thirtyFourAF_84503 : Nat.Prime 84503 := by norm_num
private theorem prime_thirtyFourAF_86243 : Nat.Prime 86243 := by norm_num
private theorem prime_thirtyFourAF_97943 : Nat.Prime 97943 := by norm_num
private theorem prime_thirtyFourAF_108223 : Nat.Prime 108223 := by norm_num
private theorem prime_thirtyFourAF_110069 : Nat.Prime 110069 := by norm_num
private theorem prime_thirtyFourAF_117361 : Nat.Prime 117361 := by norm_num
private theorem prime_thirtyFourAF_119447 : Nat.Prime 119447 := by norm_num
private theorem prime_thirtyFourAF_121343 : Nat.Prime 121343 := by norm_num
private theorem prime_thirtyFourAF_126641 : Nat.Prime 126641 := by norm_num
private theorem prime_thirtyFourAF_127343 : Nat.Prime 127343 := by norm_num
private theorem prime_thirtyFourAF_129119 : Nat.Prime 129119 := by norm_num
private theorem prime_thirtyFourAF_129277 : Nat.Prime 129277 := by norm_num
private theorem prime_thirtyFourAF_131899 : Nat.Prime 131899 := by norm_num
private theorem prime_thirtyFourAF_133657 : Nat.Prime 133657 := by norm_num
private theorem prime_thirtyFourAF_136601 : Nat.Prime 136601 := by norm_num
private theorem prime_thirtyFourAF_141023 : Nat.Prime 141023 := by norm_num
private theorem prime_thirtyFourAF_159421 : Nat.Prime 159421 := by norm_num
private theorem prime_thirtyFourAF_162917 : Nat.Prime 162917 := by norm_num
private theorem prime_thirtyFourAF_163417 : Nat.Prime 163417 := by norm_num
private theorem prime_thirtyFourAF_163561 : Nat.Prime 163561 := by norm_num
private theorem prime_thirtyFourAF_172307 : Nat.Prime 172307 := by norm_num
private theorem prime_thirtyFourAF_179411 : Nat.Prime 179411 := by norm_num
private theorem prime_thirtyFourAF_187477 : Nat.Prime 187477 := by norm_num
private theorem prime_thirtyFourAF_188473 : Nat.Prime 188473 := by norm_num
private theorem prime_thirtyFourAF_197969 : Nat.Prime 197969 := by norm_num
private theorem prime_thirtyFourAF_201997 : Nat.Prime 201997 := by norm_num
private theorem prime_thirtyFourAF_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_thirtyFourAF_212081 : Nat.Prime 212081 := by norm_num
private theorem prime_thirtyFourAF_215587 : Nat.Prime 215587 := by norm_num
private theorem prime_thirtyFourAF_216179 : Nat.Prime 216179 := by norm_num
private theorem prime_thirtyFourAF_223283 : Nat.Prime 223283 := by norm_num
private theorem prime_thirtyFourAF_231841 : Nat.Prime 231841 := by norm_num
private theorem prime_thirtyFourAF_236723 : Nat.Prime 236723 := by norm_num
private theorem prime_thirtyFourAF_244429 : Nat.Prime 244429 := by norm_num
private theorem prime_thirtyFourAF_291923 : Nat.Prime 291923 := by norm_num
private theorem prime_thirtyFourAF_299027 : Nat.Prime 299027 := by norm_num
private theorem prime_thirtyFourAF_299311 : Nat.Prime 299311 := by norm_num
private theorem prime_thirtyFourAF_316801 : Nat.Prime 316801 := by norm_num
private theorem prime_thirtyFourAF_327263 : Nat.Prime 327263 := by norm_num
private theorem prime_thirtyFourAF_331447 : Nat.Prime 331447 := by norm_num
private theorem prime_thirtyFourAF_338269 : Nat.Prime 338269 := by norm_num
private theorem prime_thirtyFourAF_352237 : Nat.Prime 352237 := by norm_num
private theorem prime_thirtyFourAF_353057 : Nat.Prime 353057 := by norm_num
private theorem prime_thirtyFourAF_355541 : Nat.Prime 355541 := by norm_num
private theorem prime_thirtyFourAF_365983 : Nat.Prime 365983 := by norm_num
private theorem prime_thirtyFourAF_379571 : Nat.Prime 379571 := by norm_num
private theorem prime_thirtyFourAF_391073 : Nat.Prime 391073 := by norm_num
private theorem prime_thirtyFourAF_398731 : Nat.Prime 398731 := by norm_num
private theorem prime_thirtyFourAF_404177 : Nat.Prime 404177 := by norm_num
private theorem prime_thirtyFourAF_413197 : Nat.Prime 413197 := by norm_num
private theorem prime_thirtyFourAF_413461 : Nat.Prime 413461 := by norm_num
private theorem prime_thirtyFourAF_426407 : Nat.Prime 426407 := by norm_num
private theorem prime_thirtyFourAF_439441 : Nat.Prime 439441 := by norm_num
private theorem prime_thirtyFourAF_442109 : Nat.Prime 442109 := by norm_num
private theorem prime_thirtyFourAF_449671 : Nat.Prime 449671 := by norm_num
private theorem prime_thirtyFourAF_514309 : Nat.Prime 514309 := by norm_num
private theorem prime_thirtyFourAF_518233 : Nat.Prime 518233 := by norm_num
private theorem prime_thirtyFourAF_521281 : Nat.Prime 521281 := by norm_num
private theorem prime_thirtyFourAF_572791 : Nat.Prime 572791 := by norm_num
private theorem prime_thirtyFourAF_588061 : Nat.Prime 588061 := by norm_num
private theorem prime_thirtyFourAF_588881 : Nat.Prime 588881 := by norm_num
private theorem prime_thirtyFourAF_617363 : Nat.Prime 617363 := by norm_num
private theorem prime_thirtyFourAF_627481 : Nat.Prime 627481 := by norm_num
private theorem prime_thirtyFourAF_635617 : Nat.Prime 635617 := by norm_num
private theorem prime_thirtyFourAF_659171 : Nat.Prime 659171 := by norm_num
private theorem prime_thirtyFourAF_664879 : Nat.Prime 664879 := by norm_num
private theorem prime_thirtyFourAF_693503 : Nat.Prime 693503 := by norm_num
private theorem prime_thirtyFourAF_729413 : Nat.Prime 729413 := by norm_num
private theorem prime_thirtyFourAF_763157 : Nat.Prime 763157 := by norm_num
private theorem prime_thirtyFourAF_801217 : Nat.Prime 801217 := by norm_num
private theorem prime_thirtyFourAF_831643 : Nat.Prime 831643 := by norm_num
private theorem prime_thirtyFourAF_851549 : Nat.Prime 851549 := by norm_num
private theorem prime_thirtyFourAF_858083 : Nat.Prime 858083 := by norm_num
private theorem prime_thirtyFourAF_865643 : Nat.Prime 865643 := by norm_num
private theorem prime_thirtyFourAF_918793 : Nat.Prime 918793 := by norm_num
private theorem prime_thirtyFourAF_1062361 : Nat.Prime 1062361 := by norm_num
private theorem prime_thirtyFourAF_1076753 : Nat.Prime 1076753 := by norm_num
private theorem prime_thirtyFourAF_1133689 : Nat.Prime 1133689 := by norm_num
private theorem prime_thirtyFourAF_1167833 : Nat.Prime 1167833 := by norm_num
private theorem prime_thirtyFourAF_1193693 : Nat.Prime 1193693 := by norm_num
private theorem prime_thirtyFourAF_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_thirtyFourAF_1231261 : Nat.Prime 1231261 := by norm_num
private theorem prime_thirtyFourAF_1340981 : Nat.Prime 1340981 := by norm_num
private theorem prime_thirtyFourAF_1383593 : Nat.Prime 1383593 := by norm_num
private theorem prime_thirtyFourAF_1431307 : Nat.Prime 1431307 := by norm_num
private theorem prime_thirtyFourAF_1479133 : Nat.Prime 1479133 := by norm_num
private theorem prime_thirtyFourAF_1553471 : Nat.Prime 1553471 := by norm_num
private theorem prime_thirtyFourAF_1563083 : Nat.Prime 1563083 := by norm_num
private theorem prime_thirtyFourAF_1610527 : Nat.Prime 1610527 := by norm_num
private theorem prime_thirtyFourAF_1646189 : Nat.Prime 1646189 := by norm_num
private theorem prime_thirtyFourAF_1670623 : Nat.Prime 1670623 := by norm_num
private theorem prime_thirtyFourAF_1842727 : Nat.Prime 1842727 := by norm_num
private theorem prime_thirtyFourAF_1850837 : Nat.Prime 1850837 := by norm_num
private theorem prime_thirtyFourAF_1855421 : Nat.Prime 1855421 := by norm_num
private theorem prime_thirtyFourAF_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_thirtyFourAF_2432869 : Nat.Prime 2432869 := by norm_num
private theorem prime_thirtyFourAF_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_thirtyFourAF_2577623 : Nat.Prime 2577623 := by norm_num
private theorem prime_thirtyFourAF_2668903 : Nat.Prime 2668903 := by norm_num
private theorem prime_thirtyFourAF_2771257 : Nat.Prime 2771257 := by norm_num
private theorem prime_thirtyFourAF_2862163 : Nat.Prime 2862163 := by norm_num
private theorem prime_thirtyFourAF_2990957 : Nat.Prime 2990957 := by norm_num
private theorem prime_thirtyFourAF_3033883 : Nat.Prime 3033883 := by norm_num
private theorem prime_thirtyFourAF_3395999 : Nat.Prime 3395999 := by norm_num
private theorem prime_thirtyFourAF_3534187 : Nat.Prime 3534187 := by norm_num
private theorem prime_thirtyFourAF_3606989 : Nat.Prime 3606989 := by norm_num
private theorem prime_thirtyFourAF_3735763 : Nat.Prime 3735763 := by norm_num
private theorem prime_thirtyFourAF_3794083 : Nat.Prime 3794083 := by norm_num
private theorem prime_thirtyFourAF_3960137 : Nat.Prime 3960137 := by norm_num
private theorem prime_thirtyFourAF_4220893 : Nat.Prime 4220893 := by norm_num
private theorem prime_thirtyFourAF_4930417 : Nat.Prime 4930417 := by norm_num
private theorem prime_thirtyFourAF_5261647 : Nat.Prime 5261647 := by norm_num
private theorem prime_thirtyFourAF_5468921 : Nat.Prime 5468921 := by norm_num
private theorem prime_thirtyFourAF_6019571 : Nat.Prime 6019571 := by norm_num
private theorem prime_thirtyFourAF_6163957 : Nat.Prime 6163957 := by norm_num
private theorem prime_thirtyFourAF_6549019 : Nat.Prime 6549019 := by norm_num
private theorem prime_thirtyFourAF_6765023 : Nat.Prime 6765023 := by norm_num
private theorem prime_thirtyFourAF_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtyFourAF_7303909 : Nat.Prime 7303909 := by norm_num
private theorem prime_thirtyFourAF_7661581 : Nat.Prime 7661581 := by norm_num
private theorem prime_thirtyFourAF_7727273 : Nat.Prime 7727273 := by norm_num
private theorem prime_thirtyFourAF_7991941 : Nat.Prime 7991941 := by norm_num
private theorem prime_thirtyFourAF_8511353 : Nat.Prime 8511353 := by norm_num
private theorem prime_thirtyFourAF_8574737 : Nat.Prime 8574737 := by norm_num
private theorem prime_thirtyFourAF_8767271 : Nat.Prime 8767271 := by norm_num
private theorem prime_thirtyFourAF_8801467 : Nat.Prime 8801467 := by norm_num
private theorem prime_thirtyFourAF_9229411 : Nat.Prime 9229411 := by norm_num
private theorem prime_thirtyFourAF_9978323 : Nat.Prime 9978323 := by norm_num
private theorem prime_thirtyFourAF_10469639 : Nat.Prime 10469639 := by norm_num
private theorem prime_thirtyFourAF_11431993 : Nat.Prime 11431993 := by norm_num
private theorem prime_thirtyFourAF_11452853 : Nat.Prime 11452853 := by norm_num
private theorem prime_thirtyFourAF_11475509 : Nat.Prime 11475509 := by norm_num
private theorem prime_thirtyFourAF_11713441 : Nat.Prime 11713441 := by norm_num
private theorem prime_thirtyFourAF_11872057 : Nat.Prime 11872057 := by norm_num
private theorem prime_thirtyFourAF_12309797 : Nat.Prime 12309797 := by norm_num
private theorem prime_thirtyFourAF_12640889 : Nat.Prime 12640889 := by norm_num
private theorem prime_thirtyFourAF_13072109 : Nat.Prime 13072109 := by norm_num
private theorem prime_thirtyFourAF_13251499 : Nat.Prime 13251499 := by norm_num
private theorem prime_thirtyFourAF_13595389 : Nat.Prime 13595389 := by norm_num
private theorem prime_thirtyFourAF_13785511 : Nat.Prime 13785511 := by norm_num
private theorem prime_thirtyFourAF_13879277 : Nat.Prime 13879277 := by norm_num
private theorem prime_thirtyFourAF_14940509 : Nat.Prime 14940509 := by norm_num
private theorem prime_thirtyFourAF_16046729 : Nat.Prime 16046729 := by norm_num
private theorem prime_thirtyFourAF_16425091 : Nat.Prime 16425091 := by norm_num
private theorem prime_thirtyFourAF_17562977 : Nat.Prime 17562977 := by norm_num
private theorem prime_thirtyFourAF_19131283 : Nat.Prime 19131283 := by norm_num
private theorem prime_thirtyFourAF_21073271 : Nat.Prime 21073271 := by norm_num
private theorem prime_thirtyFourAF_21642461 : Nat.Prime 21642461 := by norm_num
private theorem prime_thirtyFourAF_22723003 : Nat.Prime 22723003 := by norm_num
private theorem prime_thirtyFourAF_27081997 : Nat.Prime 27081997 := by norm_num
private theorem prime_thirtyFourAF_27745013 : Nat.Prime 27745013 := by norm_num

private theorem prime_thirtyFourAF_30723401 : Nat.Prime 30723401 := by
  apply lucas_primality 30723401 (6 : ZMod 30723401)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (23, 1), (6679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (23, 1), (6679, 1)] : List FactorBlock).map factorBlockValue).prod) = 30723401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_6679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 30723401) ^ 15361700 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 30723401) ^ 6144680 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 30723401) ^ 1335800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 30723401) ^ 4600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_30931477 : Nat.Prime 30931477 := by
  apply lucas_primality 30931477 (2 : ZMod 30931477)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2577623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2577623, 1)] : List FactorBlock).map factorBlockValue).prod) = 30931477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_2577623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30931477) ^ 15465738 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30931477) ^ 10310492 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30931477) ^ 12 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_32896043 : Nat.Prime 32896043 := by
  apply lucas_primality 32896043 (2 : ZMod 32896043)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) = 32896043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_349
      · exact prime_thirtyFourAF_47129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32896043) ^ 16448021 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32896043) ^ 94258 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32896043) ^ 698 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_34260913 : Nat.Prime 34260913 := by
  apply lucas_primality 34260913 (13 : ZMod 34260913)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (41, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (41, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) = 34260913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 34260913) ^ 17130456 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 34260913) ^ 11420304 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 34260913) ^ 4894416 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 34260913) ^ 835632 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 34260913) ^ 41328 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_983
      · exact prime_thirtyFourAF_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_36117427 : Nat.Prime 36117427 := by
  apply lucas_primality 36117427 (3 : ZMod 36117427)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6019571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6019571, 1)] : List FactorBlock).map factorBlockValue).prod) = 36117427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_6019571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36117427) ^ 18058713 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 36117427) ^ 12039142 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 36117427) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_39135331 : Nat.Prime 39135331 := by
  apply lucas_primality 39135331 (2 : ZMod 39135331)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 2), (31, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 2), (31, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 39135331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39135331) ^ 19567665 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39135331) ^ 13045110 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39135331) ^ 7827066 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39135331) ^ 3010410 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39135331) ^ 1262430 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39135331) ^ 471510 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_41305951 : Nat.Prime 41305951 := by
  apply lucas_primality 41305951 (3 : ZMod 41305951)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (7, 1), (31, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (7, 1), (31, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 41305951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41305951) ^ 20652975 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 13768650 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 8261190 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 5900850 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 1332450 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 878850 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_42208931 : Nat.Prime 42208931 := by
  apply lucas_primality 42208931 (2 : ZMod 42208931)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4220893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4220893, 1)] : List FactorBlock).map factorBlockValue).prod) = 42208931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_4220893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42208931) ^ 21104465 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42208931) ^ 8441786 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42208931) ^ 10 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_47050259 : Nat.Prime 47050259 := by
  apply lucas_primality 47050259 (2 : ZMod 47050259)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (398731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (398731, 1)] : List FactorBlock).map factorBlockValue).prod) = 47050259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_398731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47050259) ^ 23525129 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47050259) ^ 797462 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47050259) ^ 118 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_47715119 : Nat.Prime 47715119 := by
  apply lucas_primality 47715119 (7 : ZMod 47715119)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (211, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (211, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 47715119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_211
      · exact prime_thirtyFourAF_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47715119) ^ 23857559 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 4337738 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 2511322 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 226138 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 88198 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_47951647 : Nat.Prime 47951647 := by
  apply lucas_primality 47951647 (3 : ZMod 47951647)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7991941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7991941, 1)] : List FactorBlock).map factorBlockValue).prod) = 47951647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7991941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47951647) ^ 23975823 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47951647) ^ 15983882 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47951647) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_48662543 : Nat.Prime 48662543 := by
  apply lucas_primality 48662543 (5 : ZMod 48662543)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947, 1), (25693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947, 1), (25693, 1)] : List FactorBlock).map factorBlockValue).prod) = 48662543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_947
      · exact prime_thirtyFourAF_25693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48662543) ^ 24331271 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48662543) ^ 51386 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48662543) ^ 1894 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_50928011 : Nat.Prime 50928011 := by
  apply lucas_primality 50928011 (6 : ZMod 50928011)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (631, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (631, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 50928011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_631
      · exact prime_thirtyFourAF_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 50928011) ^ 25464005 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 10185602 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 7275430 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 80710 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 44170 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_52142977 : Nat.Prime 52142977 := by
  apply lucas_primality 52142977 (5 : ZMod 52142977)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (45263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (45263, 1)] : List FactorBlock).map factorBlockValue).prod) = 52142977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_45263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52142977) ^ 26071488 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52142977) ^ 17380992 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52142977) ^ 1152 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_54381557 : Nat.Prime 54381557 := by
  apply lucas_primality 54381557 (2 : ZMod 54381557)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13595389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13595389, 1)] : List FactorBlock).map factorBlockValue).prod) = 54381557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13595389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 54381557) ^ 27190778 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54381557) ^ 4 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_55457533 : Nat.Prime 55457533 := by
  apply lucas_primality 55457533 (2 : ZMod 55457533)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (71, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (71, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) = 55457533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_71
      · exact prime_thirtyFourAF_1669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55457533) ^ 27728766 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55457533) ^ 18485844 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55457533) ^ 4265964 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55457533) ^ 781092 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55457533) ^ 33228 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_55490027 : Nat.Prime 55490027 := by
  apply lucas_primality 55490027 (2 : ZMod 55490027)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27745013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27745013, 1)] : List FactorBlock).map factorBlockValue).prod) = 55490027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_27745013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 55490027) ^ 27745013 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55490027) ^ 2 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_58035469 : Nat.Prime 58035469 := by
  apply lucas_primality 58035469 (2 : ZMod 58035469)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (81971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (81971, 1)] : List FactorBlock).map factorBlockValue).prod) = 58035469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_81971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58035469) ^ 29017734 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58035469) ^ 19345156 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58035469) ^ 983652 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58035469) ^ 708 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_59878297 : Nat.Prime 59878297 := by
  apply lucas_primality 59878297 (5 : ZMod 59878297)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (831643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (831643, 1)] : List FactorBlock).map factorBlockValue).prod) = 59878297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_831643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 59878297) ^ 29939148 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 59878297) ^ 19959432 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 59878297) ^ 72 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_62602601 : Nat.Prime 62602601 := by
  apply lucas_primality 62602601 (3 : ZMod 62602601)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (89, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (89, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 62602601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_89
      · exact prime_thirtyFourAF_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62602601) ^ 31301300 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 12520520 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 703400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 17800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_66323641 : Nat.Prime 66323641 := by
  apply lucas_primality 66323641 (7 : ZMod 66323641)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (83, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (83, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 66323641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_83
      · exact prime_thirtyFourAF_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 66323641) ^ 33161820 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 66323641) ^ 22107880 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 66323641) ^ 13264728 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 66323641) ^ 799080 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 66323641) ^ 9960 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_73627703 : Nat.Prime 73627703 := by
  apply lucas_primality 73627703 (5 : ZMod 73627703)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5281, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5281, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) = 73627703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5281
      · exact prime_thirtyFourAF_6971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73627703) ^ 36813851 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 73627703) ^ 13942 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 73627703) ^ 10562 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_75374693 : Nat.Prime 75374693 := by
  apply lucas_primality 75374693 (2 : ZMod 75374693)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (355541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (355541, 1)] : List FactorBlock).map factorBlockValue).prod) = 75374693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_355541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75374693) ^ 37687346 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 75374693) ^ 1422164 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 75374693) ^ 212 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_88685873 : Nat.Prime 88685873 := by
  apply lucas_primality 88685873 (3 : ZMod 88685873)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) = 88685873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_29641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 88685873) ^ 44342936 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 8062352 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 5216816 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 2992 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_94453091 : Nat.Prime 94453091 := by
  apply lucas_primality 94453091 (2 : ZMod 94453091)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (389, 1), (24281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (389, 1), (24281, 1)] : List FactorBlock).map factorBlockValue).prod) = 94453091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_389
      · exact prime_thirtyFourAF_24281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94453091) ^ 47226545 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94453091) ^ 18890618 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94453091) ^ 242810 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94453091) ^ 3890 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_95430239 : Nat.Prime 95430239 := by
  apply lucas_primality 95430239 (7 : ZMod 95430239)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47715119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47715119, 1)] : List FactorBlock).map factorBlockValue).prod) = 95430239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_47715119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 95430239) ^ 47715119 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 95430239) ^ 2 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_100451987 : Nat.Prime 100451987 := by
  apply lucas_primality 100451987 (2 : ZMod 100451987)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (103, 1), (5479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (103, 1), (5479, 1)] : List FactorBlock).map factorBlockValue).prod) = 100451987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_89
      · exact prime_thirtyFourAF_103
      · exact prime_thirtyFourAF_5479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100451987) ^ 50225993 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 100451987) ^ 1128674 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 100451987) ^ 975262 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 100451987) ^ 18334 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_100602899 : Nat.Prime 100602899 := by
  apply lucas_primality 100602899 (2 : ZMod 100602899)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (42737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (42737, 1)] : List FactorBlock).map factorBlockValue).prod) = 100602899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_107
      · exact prime_thirtyFourAF_42737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100602899) ^ 50301449 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 100602899) ^ 9145718 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 100602899) ^ 940214 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 100602899) ^ 2354 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_105207253 : Nat.Prime 105207253 := by
  apply lucas_primality 105207253 (2 : ZMod 105207253)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8767271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8767271, 1)] : List FactorBlock).map factorBlockValue).prod) = 105207253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_8767271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105207253) ^ 52603626 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 105207253) ^ 35069084 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 105207253) ^ 12 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_109178521 : Nat.Prime 109178521 := by
  apply lucas_primality 109178521 (23 : ZMod 109178521)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (107, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (107, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 109178521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_107
      · exact prime_thirtyFourAF_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 109178521) ^ 54589260 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 36392840 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 21835704 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 9925320 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 1020360 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 141240 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_111306893 : Nat.Prime 111306893 := by
  apply lucas_primality 111306893 (2 : ZMod 111306893)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (352237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (352237, 1)] : List FactorBlock).map factorBlockValue).prod) = 111306893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_79
      · exact prime_thirtyFourAF_352237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111306893) ^ 55653446 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111306893) ^ 1408948 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111306893) ^ 316 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_122594851 : Nat.Prime 122594851 := by
  apply lucas_primality 122594851 (2 : ZMod 122594851)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) = 122594851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_12973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122594851) ^ 61297425 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 40864950 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 24518970 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 17513550 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 9450 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_129192733 : Nat.Prime 129192733 := by
  apply lucas_primality 129192733 (2 : ZMod 129192733)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (181, 1), (2203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (181, 1), (2203, 1)] : List FactorBlock).map factorBlockValue).prod) = 129192733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_181
      · exact prime_thirtyFourAF_2203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129192733) ^ 64596366 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 129192733) ^ 43064244 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 129192733) ^ 713772 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 129192733) ^ 58644 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_133416637 : Nat.Prime 133416637 := by
  apply lucas_primality 133416637 (6 : ZMod 133416637)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) = 133416637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_241
      · exact prime_thirtyFourAF_46133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 133416637) ^ 66708318 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 44472212 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 553596 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 2892 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_139585741 : Nat.Prime 139585741 := by
  apply lucas_primality 139585741 (6 : ZMod 139585741)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (59, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (59, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 139585741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 139585741) ^ 69792870 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 139585741) ^ 46528580 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 139585741) ^ 27917148 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 139585741) ^ 19940820 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 139585741) ^ 3246180 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 139585741) ^ 2365860 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 139585741) ^ 1065540 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_154791467 : Nat.Prime 154791467 := by
  apply lucas_primality 154791467 (2 : ZMod 154791467)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (215587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (215587, 1)] : List FactorBlock).map factorBlockValue).prod) = 154791467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_359
      · exact prime_thirtyFourAF_215587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 154791467) ^ 77395733 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 154791467) ^ 431174 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 154791467) ^ 718 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_157139797 : Nat.Prime 157139797 := by
  apply lucas_primality 157139797 (2 : ZMod 157139797)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (108223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (108223, 1)] : List FactorBlock).map factorBlockValue).prod) = 157139797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_108223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157139797) ^ 78569898 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 157139797) ^ 52379932 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 157139797) ^ 14285436 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 157139797) ^ 1452 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_176901793 : Nat.Prime 176901793 := by
  apply lucas_primality 176901793 (5 : ZMod 176901793)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1842727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1842727, 1)] : List FactorBlock).map factorBlockValue).prod) = 176901793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_1842727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 176901793) ^ 88450896 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 176901793) ^ 58967264 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 176901793) ^ 96 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_184340407 : Nat.Prime 184340407 := by
  apply lucas_primality 184340407 (3 : ZMod 184340407)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30723401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30723401, 1)] : List FactorBlock).map factorBlockValue).prod) = 184340407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_30723401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 184340407) ^ 92170203 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184340407) ^ 61446802 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184340407) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_213122467 : Nat.Prime 213122467 := by
  apply lucas_primality 213122467 (2 : ZMod 213122467)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3089, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3089, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) = 213122467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_3089
      · exact prime_thirtyFourAF_3833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 213122467) ^ 106561233 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 213122467) ^ 71040822 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 213122467) ^ 68994 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 213122467) ^ 55602 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_213345877 : Nat.Prime 213345877 := by
  apply lucas_primality 213345877 (2 : ZMod 213345877)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (413461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (413461, 1)] : List FactorBlock).map factorBlockValue).prod) = 213345877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_413461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 213345877) ^ 106672938 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 213345877) ^ 71115292 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 213345877) ^ 4961532 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 213345877) ^ 516 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_228167669 : Nat.Prime 228167669 := by
  apply lucas_primality 228167669 (2 : ZMod 228167669)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (588061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (588061, 1)] : List FactorBlock).map factorBlockValue).prod) = 228167669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_97
      · exact prime_thirtyFourAF_588061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 228167669) ^ 114083834 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 228167669) ^ 2352244 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 228167669) ^ 388 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_191
      · exact prime_thirtyFourAF_383
      · exact prime_thirtyFourAF_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_282626749 : Nat.Prime 282626749 := by
  apply lucas_primality 282626749 (2 : ZMod 282626749)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (413197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (413197, 1)] : List FactorBlock).map factorBlockValue).prod) = 282626749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_413197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 282626749) ^ 141313374 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282626749) ^ 94208916 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282626749) ^ 14875092 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282626749) ^ 684 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_282861461 : Nat.Prime 282861461 := by
  apply lucas_primality 282861461 (2 : ZMod 282861461)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) = 282861461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_49279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 282861461) ^ 141430730 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 56572292 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 40408780 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 6899060 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 5740 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_304357847 : Nat.Prime 304357847 := by
  apply lucas_primality 304357847 (5 : ZMod 304357847)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (19, 1), (83, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (19, 1), (83, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 304357847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_83
      · exact prime_thirtyFourAF_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 304357847) ^ 152178923 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 23412142 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 16018834 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 3666962 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 533026 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_326289343 : Nat.Prime 326289343 := by
  apply lucas_primality 326289343 (3 : ZMod 326289343)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (54381557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (54381557, 1)] : List FactorBlock).map factorBlockValue).prod) = 326289343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_54381557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 326289343) ^ 163144671 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 326289343) ^ 108763114 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 326289343) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_344755493 : Nat.Prime 344755493 := by
  apply lucas_primality 344755493 (2 : ZMod 344755493)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (971, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (971, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 344755493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_971
      · exact prime_thirtyFourAF_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 344755493) ^ 172377746 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 9317716 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 355052 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 143708 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_393372509 : Nat.Prime 393372509 := by
  apply lucas_primality 393372509 (2 : ZMod 393372509)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (588881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (588881, 1)] : List FactorBlock).map factorBlockValue).prod) = 393372509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_167
      · exact prime_thirtyFourAF_588881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 393372509) ^ 196686254 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 393372509) ^ 2355524 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 393372509) ^ 668 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_424552907 : Nat.Prime 424552907 := by
  apply lucas_primality 424552907 (2 : ZMod 424552907)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (9229411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (9229411, 1)] : List FactorBlock).map factorBlockValue).prod) = 424552907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_9229411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 424552907) ^ 212276453 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 424552907) ^ 18458822 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 424552907) ^ 46 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_467774441 : Nat.Prime 467774441 := by
  apply lucas_primality 467774441 (3 : ZMod 467774441)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (1670623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (1670623, 1)] : List FactorBlock).map factorBlockValue).prod) = 467774441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_1670623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 467774441) ^ 233887220 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 467774441) ^ 93554888 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 467774441) ^ 66824920 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 467774441) ^ 280 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_526768633 : Nat.Prime 526768633 := by
  apply lucas_primality 526768633 (5 : ZMod 526768633)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (23, 1), (24469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (23, 1), (24469, 1)] : List FactorBlock).map factorBlockValue).prod) = 526768633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_24469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 526768633) ^ 263384316 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 526768633) ^ 175589544 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 526768633) ^ 40520664 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 526768633) ^ 22902984 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 526768633) ^ 21528 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_529326461 : Nat.Prime 529326461 := by
  apply lucas_primality 529326461 (2 : ZMod 529326461)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (131, 1), (15541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (131, 1), (15541, 1)] : List FactorBlock).map factorBlockValue).prod) = 529326461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_131
      · exact prime_thirtyFourAF_15541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 529326461) ^ 264663230 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 529326461) ^ 105865292 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 529326461) ^ 40717420 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 529326461) ^ 4040660 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 529326461) ^ 34060 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_754711099 : Nat.Prime 754711099 := by
  apply lucas_primality 754711099 (3 : ZMod 754711099)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (5468921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (5468921, 1)] : List FactorBlock).map factorBlockValue).prod) = 754711099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_5468921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 754711099) ^ 377355549 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 754711099) ^ 251570366 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 754711099) ^ 32813526 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 754711099) ^ 138 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_774668639 : Nat.Prime 774668639 := by
  apply lucas_primality 774668639 (23 : ZMod 774668639)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1663, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1663, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) = 774668639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_89
      · exact prime_thirtyFourAF_1663
      · exact prime_thirtyFourAF_2617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 774668639) ^ 387334319 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 8704142 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 465826 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 296014 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_783928043 : Nat.Prime 783928043 := by
  apply lucas_primality 783928043 (2 : ZMod 783928043)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15727, 1), (24923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15727, 1), (24923, 1)] : List FactorBlock).map factorBlockValue).prod) = 783928043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_15727
      · exact prime_thirtyFourAF_24923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 783928043) ^ 391964021 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 783928043) ^ 49846 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 783928043) ^ 31454 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_791375111 : Nat.Prime 791375111 := by
  apply lucas_primality 791375111 (7 : ZMod 791375111)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (179, 1), (442109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (179, 1), (442109, 1)] : List FactorBlock).map factorBlockValue).prod) = 791375111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_179
      · exact prime_thirtyFourAF_442109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 791375111) ^ 395687555 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 791375111) ^ 158275022 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 791375111) ^ 4421090 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 791375111) ^ 1790 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_816631843 : Nat.Prime 816631843 := by
  apply lucas_primality 816631843 (2 : ZMod 816631843)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (10469639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (10469639, 1)] : List FactorBlock).map factorBlockValue).prod) = 816631843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_10469639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 816631843) ^ 408315921 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 816631843) ^ 272210614 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 816631843) ^ 62817834 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 816631843) ^ 78 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_833538191 : Nat.Prime 833538191 := by
  apply lucas_primality 833538191 (13 : ZMod 833538191)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1399, 1), (59581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1399, 1), (59581, 1)] : List FactorBlock).map factorBlockValue).prod) = 833538191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_1399
      · exact prime_thirtyFourAF_59581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 833538191) ^ 416769095 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 833538191) ^ 166707638 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 833538191) ^ 595810 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 833538191) ^ 13990 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_838457359 : Nat.Prime 838457359 := by
  apply lucas_primality 838457359 (3 : ZMod 838457359)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (1383593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (1383593, 1)] : List FactorBlock).map factorBlockValue).prod) = 838457359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_1383593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 838457359) ^ 419228679 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 838457359) ^ 279485786 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 838457359) ^ 8301558 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 838457359) ^ 606 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_847846819 : Nat.Prime 847846819 := by
  apply lucas_primality 847846819 (7 : ZMod 847846819)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (13, 1), (47, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (13, 1), (47, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) = 847846819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_3671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 847846819) ^ 423923409 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 282615606 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 121120974 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 65218986 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 18039294 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 230958 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1015858667 : Nat.Prime 1015858667 := by
  apply lucas_primality 1015858667 (2 : ZMod 1015858667)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3929, 1), (129277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3929, 1), (129277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1015858667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3929
      · exact prime_thirtyFourAF_129277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1015858667) ^ 507929333 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1015858667) ^ 258554 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1015858667) ^ 7858 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1052072531 : Nat.Prime 1052072531 := by
  apply lucas_primality 1052072531 (6 : ZMod 1052072531)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (105207253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (105207253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1052072531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_105207253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1052072531) ^ 526036265 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052072531) ^ 210414506 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052072531) ^ 10 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1103034067 : Nat.Prime 1103034067 := by
  apply lucas_primality 1103034067 (2 : ZMod 1103034067)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1877, 1), (97943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1877, 1), (97943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103034067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_1877
      · exact prime_thirtyFourAF_97943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1103034067) ^ 551517033 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103034067) ^ 367678022 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103034067) ^ 587658 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103034067) ^ 11262 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_113
      · exact prime_thirtyFourAF_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1243269197 : Nat.Prime 1243269197 := by
  apply lucas_primality 1243269197 (2 : ZMod 1243269197)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (101, 1), (236723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (101, 1), (236723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243269197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_236723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1243269197) ^ 621634598 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243269197) ^ 95636092 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243269197) ^ 12309596 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243269197) ^ 5252 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1358805521 : Nat.Prime 1358805521 := by
  apply lucas_primality 1358805521 (3 : ZMod 1358805521)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (19, 1), (53, 1), (101, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (19, 1), (53, 1), (101, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1358805521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1358805521) ^ 679402760 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358805521) ^ 271761104 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358805521) ^ 71516080 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358805521) ^ 25637840 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358805521) ^ 13453520 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358805521) ^ 8136560 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1376407559 : Nat.Prime 1376407559 := by
  apply lucas_primality 1376407559 (7 : ZMod 1376407559)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3407, 1), (201997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3407, 1), (201997, 1)] : List FactorBlock).map factorBlockValue).prod) = 1376407559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3407
      · exact prime_thirtyFourAF_201997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1376407559) ^ 688203779 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1376407559) ^ 403994 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1376407559) ^ 6814 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1531464617 : Nat.Prime 1531464617 := by
  apply lucas_primality 1531464617 (3 : ZMod 1531464617)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (101, 1), (172307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (101, 1), (172307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531464617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_172307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1531464617) ^ 765732308 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 139224056 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 15163016 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 8888 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1588277671 : Nat.Prime 1588277671 := by
  apply lucas_primality 1588277671 (7 : ZMod 1588277671)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588277671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_25127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1588277671) ^ 794138835 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 529425890 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 317655534 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 226896810 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 36936690 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 63210 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1839610193 : Nat.Prime 1839610193 := by
  apply lucas_primality 1839610193 (3 : ZMod 1839610193)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (16425091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (16425091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1839610193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_16425091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1839610193) ^ 919805096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839610193) ^ 262801456 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839610193) ^ 112 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1898759389 : Nat.Prime 1898759389 := by
  apply lucas_primality 1898759389 (2 : ZMod 1898759389)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (307, 1), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (307, 1), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898759389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_307
      · exact prime_thirtyFourAF_22409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1898759389) ^ 949379694 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 632919796 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 82554756 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 6184884 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 84732 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2179651489 : Nat.Prime 2179651489 := by
  apply lucas_primality 2179651489 (19 : ZMod 2179651489)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (23, 1), (141023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (23, 1), (141023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179651489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_141023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2179651489) ^ 1089825744 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 726550496 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 311378784 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 94767456 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 15456 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2389974799 : Nat.Prime 2389974799 := by
  apply lucas_primality 2389974799 (3 : ZMod 2389974799)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5779, 1), (68927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5779, 1), (68927, 1)] : List FactorBlock).map factorBlockValue).prod) = 2389974799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5779
      · exact prime_thirtyFourAF_68927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2389974799) ^ 1194987399 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389974799) ^ 796658266 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389974799) ^ 413562 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389974799) ^ 34674 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2691438983 : Nat.Prime 2691438983 := by
  apply lucas_primality 2691438983 (5 : ZMod 2691438983)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3677, 1), (365983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3677, 1), (365983, 1)] : List FactorBlock).map factorBlockValue).prod) = 2691438983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3677
      · exact prime_thirtyFourAF_365983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2691438983) ^ 1345719491 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2691438983) ^ 731966 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2691438983) ^ 7354 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2951252771 : Nat.Prime 2951252771 := by
  apply lucas_primality 2951252771 (2 : ZMod 2951252771)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (3735763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (3735763, 1)] : List FactorBlock).map factorBlockValue).prod) = 2951252771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_79
      · exact prime_thirtyFourAF_3735763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2951252771) ^ 1475626385 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951252771) ^ 590250554 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951252771) ^ 37357630 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951252771) ^ 790 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3193766699 : Nat.Prime 3193766699 := by
  apply lucas_primality 3193766699 (2 : ZMod 3193766699)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26227, 1), (60887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26227, 1), (60887, 1)] : List FactorBlock).map factorBlockValue).prod) = 3193766699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_26227
      · exact prime_thirtyFourAF_60887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3193766699) ^ 1596883349 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3193766699) ^ 121774 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3193766699) ^ 52454 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3194347367 : Nat.Prime 3194347367 := by
  apply lucas_primality 3194347367 (7 : ZMod 3194347367)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (228167669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (228167669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3194347367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_228167669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3194347367) ^ 1597173683 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3194347367) ^ 456335338 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3194347367) ^ 14 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3544788469 : Nat.Prime 3544788469 := by
  apply lucas_primality 3544788469 (2 : ZMod 3544788469)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (22723003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (22723003, 1)] : List FactorBlock).map factorBlockValue).prod) = 3544788469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_22723003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3544788469) ^ 1772394234 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3544788469) ^ 1181596156 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3544788469) ^ 272676036 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3544788469) ^ 156 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3880233977 : Nat.Prime 3880233977 := by
  apply lucas_primality 3880233977 (3 : ZMod 3880233977)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2287, 1), (212081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2287, 1), (212081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3880233977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_2287
      · exact prime_thirtyFourAF_212081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3880233977) ^ 1940116988 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880233977) ^ 1696648 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880233977) ^ 18296 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_4105146907 : Nat.Prime 4105146907 := by
  apply lucas_primality 4105146907 (3 : ZMod 4105146907)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (53, 1), (167, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (53, 1), (167, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 4105146907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_167
      · exact prime_thirtyFourAF_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4105146907) ^ 2052573453 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105146907) ^ 1368382302 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105146907) ^ 586449558 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105146907) ^ 77455602 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105146907) ^ 24581718 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105146907) ^ 10037034 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_5450819747 : Nat.Prime 5450819747 := by
  apply lucas_primality 5450819747 (2 : ZMod 5450819747)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (199, 1), (271, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (199, 1), (271, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 5450819747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_97
      · exact prime_thirtyFourAF_199
      · exact prime_thirtyFourAF_271
      · exact prime_thirtyFourAF_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5450819747) ^ 2725409873 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5450819747) ^ 56194018 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5450819747) ^ 27391054 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5450819747) ^ 20113726 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5450819747) ^ 10462226 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_5967429077 : Nat.Prime 5967429077 := by
  apply lucas_primality 5967429077 (2 : ZMod 5967429077)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (213122467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (213122467, 1)] : List FactorBlock).map factorBlockValue).prod) = 5967429077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_213122467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5967429077) ^ 2983714538 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5967429077) ^ 852489868 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5967429077) ^ 28 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_6860556407 : Nat.Prime 6860556407 := by
  apply lucas_primality 6860556407 (5 : ZMod 6860556407)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5839, 1), (53407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5839, 1), (53407, 1)] : List FactorBlock).map factorBlockValue).prod) = 6860556407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_5839
      · exact prime_thirtyFourAF_53407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6860556407) ^ 3430278203 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6860556407) ^ 623686946 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6860556407) ^ 1174954 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6860556407) ^ 128458 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_6886286111 : Nat.Prime 6886286111 := by
  apply lucas_primality 6886286111 (11 : ZMod 6886286111)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (62602601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (62602601, 1)] : List FactorBlock).map factorBlockValue).prod) = 6886286111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_62602601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6886286111) ^ 3443143055 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 1377257222 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 626026010 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 110 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_7237965619 : Nat.Prime 7237965619 := by
  apply lucas_primality 7237965619 (2 : ZMod 7237965619)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (30931477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (30931477, 1)] : List FactorBlock).map factorBlockValue).prod) = 7237965619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_30931477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7237965619) ^ 3618982809 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7237965619) ^ 2412655206 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7237965619) ^ 556766586 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7237965619) ^ 234 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_8080822741 : Nat.Prime 8080822741 := by
  apply lucas_primality 8080822741 (7 : ZMod 8080822741)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (244429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (244429, 1)] : List FactorBlock).map factorBlockValue).prod) = 8080822741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_244429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8080822741) ^ 4040411370 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8080822741) ^ 2693607580 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8080822741) ^ 1616164548 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8080822741) ^ 425306460 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8080822741) ^ 278649060 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8080822741) ^ 33060 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_8431932199 : Nat.Prime 8431932199 := by
  apply lucas_primality 8431932199 (3 : ZMod 8431932199)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (491, 1), (2862163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (491, 1), (2862163, 1)] : List FactorBlock).map factorBlockValue).prod) = 8431932199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_491
      · exact prime_thirtyFourAF_2862163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8431932199) ^ 4215966099 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8431932199) ^ 2810644066 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8431932199) ^ 17172978 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8431932199) ^ 2946 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_8766968939 : Nat.Prime 8766968939 := by
  apply lucas_primality 8766968939 (2 : ZMod 8766968939)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (47, 1), (137, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (47, 1), (137, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8766968939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_137
      · exact prime_thirtyFourAF_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8766968939) ^ 4383484469 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 1252424134 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 674382226 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 186531254 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 63992474 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 1171898 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_9087309221 : Nat.Prime 9087309221 := by
  apply lucas_primality 9087309221 (10 : ZMod 9087309221)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (41305951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (41305951, 1)] : List FactorBlock).map factorBlockValue).prod) = 9087309221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_41305951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 9087309221) ^ 4543654610 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 9087309221) ^ 1817461844 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 9087309221) ^ 826119020 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 9087309221) ^ 220 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_9521099779 : Nat.Prime 9521099779 := by
  apply lucas_primality 9521099779 (2 : ZMod 9521099779)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (3534187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (3534187, 1)] : List FactorBlock).map factorBlockValue).prod) = 9521099779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_449
      · exact prime_thirtyFourAF_3534187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9521099779) ^ 4760549889 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9521099779) ^ 3173699926 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9521099779) ^ 21205122 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9521099779) ^ 2694 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_9564358091 : Nat.Prime 9564358091 := by
  apply lucas_primality 9564358091 (2 : ZMod 9564358091)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (83, 1), (1646189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (83, 1), (1646189, 1)] : List FactorBlock).map factorBlockValue).prod) = 9564358091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_83
      · exact prime_thirtyFourAF_1646189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9564358091) ^ 4782179045 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 1912871618 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 1366336870 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 115233230 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 5810 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_11006777017 : Nat.Prime 11006777017 := by
  apply lucas_primality 11006777017 (7 : ZMod 11006777017)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (41, 1), (97, 1), (4271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (41, 1), (97, 1), (4271, 1)] : List FactorBlock).map factorBlockValue).prod) = 11006777017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_97
      · exact prime_thirtyFourAF_4271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11006777017) ^ 5503388508 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 11006777017) ^ 3668925672 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 11006777017) ^ 268457976 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 11006777017) ^ 113471928 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 11006777017) ^ 2577096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_11635605481 : Nat.Prime 11635605481 := by
  apply lucas_primality 11635605481 (13 : ZMod 11635605481)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (113, 1), (858083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (113, 1), (858083, 1)] : List FactorBlock).map factorBlockValue).prod) = 11635605481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_113
      · exact prime_thirtyFourAF_858083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 11635605481) ^ 5817802740 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11635605481) ^ 3878535160 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11635605481) ^ 2327121096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11635605481) ^ 102969960 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11635605481) ^ 13560 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_11747183939 : Nat.Prime 11747183939 := by
  apply lucas_primality 11747183939 (2 : ZMod 11747183939)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (521, 1), (1610527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (521, 1), (1610527, 1)] : List FactorBlock).map factorBlockValue).prod) = 11747183939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_521
      · exact prime_thirtyFourAF_1610527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11747183939) ^ 5873591969 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 1678169134 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 22547378 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 7294 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_11924993071 : Nat.Prime 11924993071 := by
  apply lucas_primality 11924993071 (3 : ZMod 11924993071)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (37, 1), (1193693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (37, 1), (1193693, 1)] : List FactorBlock).map factorBlockValue).prod) = 11924993071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_1193693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11924993071) ^ 5962496535 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11924993071) ^ 3974997690 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11924993071) ^ 2384998614 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11924993071) ^ 322297110 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11924993071) ^ 9990 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_12048401357 : Nat.Prime 12048401357 := by
  apply lucas_primality 12048401357 (2 : ZMod 12048401357)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (11452853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (11452853, 1)] : List FactorBlock).map factorBlockValue).prod) = 12048401357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_263
      · exact prime_thirtyFourAF_11452853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12048401357) ^ 6024200678 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12048401357) ^ 45811412 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12048401357) ^ 1052 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_14266618679 : Nat.Prime 14266618679 := by
  apply lucas_primality 14266618679 (11 : ZMod 14266618679)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (42208931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (42208931, 1)] : List FactorBlock).map factorBlockValue).prod) = 14266618679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_42208931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 14266618679) ^ 7133309339 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 14266618679) ^ 1097432206 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 14266618679) ^ 338 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_18522816023 : Nat.Prime 18522816023 := by
  apply lucas_primality 18522816023 (5 : ZMod 18522816023)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (55457533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (55457533, 1)] : List FactorBlock).map factorBlockValue).prod) = 18522816023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_167
      · exact prime_thirtyFourAF_55457533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18522816023) ^ 9261408011 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18522816023) ^ 110915066 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18522816023) ^ 334 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_18556467049 : Nat.Prime 18556467049 := by
  apply lucas_primality 18556467049 (11 : ZMod 18556467049)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (97, 1), (379571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (97, 1), (379571, 1)] : List FactorBlock).map factorBlockValue).prod) = 18556467049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_97
      · exact prime_thirtyFourAF_379571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18556467049) ^ 9278233524 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 6185489016 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 2650923864 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 191303784 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 48888 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_18577644563 : Nat.Prime 18577644563 := by
  apply lucas_primality 18577644563 (2 : ZMod 18577644563)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (9973, 1), (22717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (9973, 1), (22717, 1)] : List FactorBlock).map factorBlockValue).prod) = 18577644563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_9973
      · exact prime_thirtyFourAF_22717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18577644563) ^ 9288822281 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18577644563) ^ 453113282 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18577644563) ^ 1862794 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18577644563) ^ 817786 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_18794905919 : Nat.Prime 18794905919 := by
  apply lucas_primality 18794905919 (11 : ZMod 18794905919)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (27081997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (27081997, 1)] : List FactorBlock).map factorBlockValue).prod) = 18794905919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_347
      · exact prime_thirtyFourAF_27081997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 18794905919) ^ 9397452959 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18794905919) ^ 54163994 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18794905919) ^ 694 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_20699526191 : Nat.Prime 20699526191 := by
  apply lucas_primality 20699526191 (7 : ZMod 20699526191)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (43, 1), (109, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (43, 1), (109, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) = 20699526191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_109
      · exact prime_thirtyFourAF_9013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20699526191) ^ 10349763095 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 4139905238 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 2957075170 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 481384330 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 189903910 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 2296630 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_21764550497 : Nat.Prime 21764550497 := by
  apply lucas_primality 21764550497 (3 : ZMod 21764550497)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (151, 1), (317, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (151, 1), (317, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 21764550497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_151
      · exact prime_thirtyFourAF_317
      · exact prime_thirtyFourAF_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21764550497) ^ 10882275248 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 1674196192 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 144136096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 68657888 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 19912672 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_21934177247 : Nat.Prime 21934177247 := by
  apply lucas_primality 21934177247 (5 : ZMod 21934177247)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1279, 1), (8574737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1279, 1), (8574737, 1)] : List FactorBlock).map factorBlockValue).prod) = 21934177247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_1279
      · exact prime_thirtyFourAF_8574737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 21934177247) ^ 10967088623 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21934177247) ^ 17149474 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21934177247) ^ 2558 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_32186861237 : Nat.Prime 32186861237 := by
  apply lucas_primality 32186861237 (2 : ZMod 32186861237)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (283, 1), (693503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (283, 1), (693503, 1)] : List FactorBlock).map factorBlockValue).prod) = 32186861237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_283
      · exact prime_thirtyFourAF_693503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32186861237) ^ 16093430618 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32186861237) ^ 785045396 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32186861237) ^ 113734492 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32186861237) ^ 46412 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_39568669331 : Nat.Prime 39568669331 := by
  apply lucas_primality 39568669331 (2 : ZMod 39568669331)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1097, 1), (3606989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1097, 1), (3606989, 1)] : List FactorBlock).map factorBlockValue).prod) = 39568669331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_1097
      · exact prime_thirtyFourAF_3606989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39568669331) ^ 19784334665 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 7913733866 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 36069890 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 10970 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_44747768707 : Nat.Prime 44747768707 := by
  apply lucas_primality 44747768707 (2 : ZMod 44747768707)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (13785511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (13785511, 1)] : List FactorBlock).map factorBlockValue).prod) = 44747768707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_541
      · exact prime_thirtyFourAF_13785511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44747768707) ^ 22373884353 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 44747768707) ^ 14915922902 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 44747768707) ^ 82713066 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 44747768707) ^ 3246 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_151
      · exact prime_thirtyFourAF_479
      · exact prime_thirtyFourAF_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_47913011609 : Nat.Prime 47913011609 := by
  apply lucas_primality 47913011609 (3 : ZMod 47913011609)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (641, 1), (121343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (641, 1), (121343, 1)] : List FactorBlock).map factorBlockValue).prod) = 47913011609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_641
      · exact prime_thirtyFourAF_121343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47913011609) ^ 23956505804 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47913011609) ^ 6844715944 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47913011609) ^ 4355728328 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47913011609) ^ 74747288 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47913011609) ^ 394856 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_49153528429 : Nat.Prime 49153528429 := by
  apply lucas_primality 49153528429 (2 : ZMod 49153528429)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (61, 1), (1061, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (61, 1), (1061, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) = 49153528429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_61
      · exact prime_thirtyFourAF_1061
      · exact prime_thirtyFourAF_3331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49153528429) ^ 24576764214 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 16384509476 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 2587027812 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 805795548 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 46327548 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 14756388 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_54703844669 : Nat.Prime 54703844669 := by
  apply lucas_primality 54703844669 (2 : ZMod 54703844669)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1243269197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1243269197, 1)] : List FactorBlock).map factorBlockValue).prod) = 54703844669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_1243269197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54703844669) ^ 27351922334 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54703844669) ^ 4973076788 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54703844669) ^ 44 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_65438880853 : Nat.Prime 65438880853 := by
  apply lucas_primality 65438880853 (5 : ZMod 65438880853)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (443, 1), (12309797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (443, 1), (12309797, 1)] : List FactorBlock).map factorBlockValue).prod) = 65438880853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_443
      · exact prime_thirtyFourAF_12309797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65438880853) ^ 32719440426 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 65438880853) ^ 21812960284 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 65438880853) ^ 147717564 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 65438880853) ^ 5316 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_96047789699 : Nat.Prime 96047789699 := by
  apply lucas_primality 96047789699 (2 : ZMod 96047789699)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6860556407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6860556407, 1)] : List FactorBlock).map factorBlockValue).prod) = 96047789699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_6860556407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96047789699) ^ 48023894849 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 96047789699) ^ 13721112814 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 96047789699) ^ 14 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_111179436971 : Nat.Prime 111179436971 := by
  apply lucas_primality 111179436971 (2 : ZMod 111179436971)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1588277671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1588277671, 1)] : List FactorBlock).map factorBlockValue).prod) = 111179436971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_1588277671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111179436971) ^ 55589718485 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 22235887394 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 15882776710 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 70 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_122684585791 : Nat.Prime 122684585791 := by
  apply lucas_primality 122684585791 (6 : ZMod 122684585791)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1051, 1), (299311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1051, 1), (299311, 1)] : List FactorBlock).map factorBlockValue).prod) = 122684585791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_1051
      · exact prime_thirtyFourAF_299311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 122684585791) ^ 61342292895 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 40894861930 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 24536917158 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 9437275830 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 116731290 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 409890 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_130041294599 : Nat.Prime 130041294599 := by
  apply lucas_primality 130041294599 (13 : ZMod 130041294599)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (467774441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (467774441, 1)] : List FactorBlock).map factorBlockValue).prod) = 130041294599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_139
      · exact prime_thirtyFourAF_467774441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 130041294599) ^ 65020647299 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 130041294599) ^ 935548882 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 130041294599) ^ 278 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_145849248859 : Nat.Prime 145849248859 := by
  apply lucas_primality 145849248859 (3 : ZMod 145849248859)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1627, 1), (14940509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1627, 1), (14940509, 1)] : List FactorBlock).map factorBlockValue).prod) = 145849248859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_1627
      · exact prime_thirtyFourAF_14940509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 145849248859) ^ 72924624429 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849248859) ^ 48616416286 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849248859) ^ 89643054 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849248859) ^ 9762 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_146634385643 : Nat.Prime 146634385643 := by
  apply lucas_primality 146634385643 (2 : ZMod 146634385643)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (187477, 1), (391073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (187477, 1), (391073, 1)] : List FactorBlock).map factorBlockValue).prod) = 146634385643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_187477
      · exact prime_thirtyFourAF_391073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 146634385643) ^ 73317192821 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 146634385643) ^ 782146 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 146634385643) ^ 374954 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_169619499827 : Nat.Prime 169619499827 := by
  apply lucas_primality 169619499827 (2 : ZMod 169619499827)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (526768633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (526768633, 1)] : List FactorBlock).map factorBlockValue).prod) = 169619499827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_526768633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 169619499827) ^ 84809749913 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 169619499827) ^ 24231357118 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 169619499827) ^ 7374760862 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 169619499827) ^ 322 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_189706644289 : Nat.Prime 189706644289 := by
  apply lucas_primality 189706644289 (11 : ZMod 189706644289)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (7, 1), (47050259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (7, 1), (47050259, 1)] : List FactorBlock).map factorBlockValue).prod) = 189706644289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_47050259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 189706644289) ^ 94853322144 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 189706644289) ^ 63235548096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 189706644289) ^ 27100949184 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 189706644289) ^ 4032 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_262367120149 : Nat.Prime 262367120149 := by
  apply lucas_primality 262367120149 (14 : ZMod 262367120149)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (727, 1), (1069, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (727, 1), (1069, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) = 262367120149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_727
      · exact prime_thirtyFourAF_1069
      · exact prime_thirtyFourAF_4019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 262367120149) ^ 131183560074 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 87455706716 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 37481017164 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 360890124 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 245432292 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 65281692 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_268254770561 : Nat.Prime 268254770561 := by
  apply lucas_primality 268254770561 (3 : ZMod 268254770561)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (59878297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (59878297, 1)] : List FactorBlock).map factorBlockValue).prod) = 268254770561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_59878297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 268254770561) ^ 134127385280 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 268254770561) ^ 53650954112 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 268254770561) ^ 38322110080 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 268254770561) ^ 4480 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_336886024471 : Nat.Prime 336886024471 := by
  apply lucas_primality 336886024471 (3 : ZMod 336886024471)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (149, 1), (601, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (149, 1), (601, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) = 336886024471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_89
      · exact prime_thirtyFourAF_149
      · exact prime_thirtyFourAF_601
      · exact prime_thirtyFourAF_1409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 336886024471) ^ 168443012235 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336886024471) ^ 112295341490 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336886024471) ^ 67377204894 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336886024471) ^ 3785236230 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336886024471) ^ 2260980030 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336886024471) ^ 560542470 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336886024471) ^ 239095830 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_338021059213 : Nat.Prime 338021059213 := by
  apply lucas_primality 338021059213 (2 : ZMod 338021059213)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (227, 1), (617363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (227, 1), (617363, 1)] : List FactorBlock).map factorBlockValue).prod) = 338021059213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_67
      · exact prime_thirtyFourAF_227
      · exact prime_thirtyFourAF_617363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338021059213) ^ 169010529606 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 112673686404 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 5045090436 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 1489079556 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 547524 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_340964828623 : Nat.Prime 340964828623 := by
  apply lucas_primality 340964828623 (5 : ZMod 340964828623)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (97, 2), (61007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (97, 2), (61007, 1)] : List FactorBlock).map factorBlockValue).prod) = 340964828623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_97
      · exact prime_thirtyFourAF_61007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 340964828623) ^ 170482414311 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340964828623) ^ 113654942874 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340964828623) ^ 30996802602 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340964828623) ^ 3515101326 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340964828623) ^ 5588946 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_344170932431 : Nat.Prime 344170932431 := by
  apply lucas_primality 344170932431 (7 : ZMod 344170932431)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (223, 1), (11872057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (223, 1), (11872057, 1)] : List FactorBlock).map factorBlockValue).prod) = 344170932431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_223
      · exact prime_thirtyFourAF_11872057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 344170932431) ^ 172085466215 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 344170932431) ^ 68834186486 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 344170932431) ^ 26474687110 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 344170932431) ^ 1543367410 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 344170932431) ^ 28990 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_370718366209 : Nat.Prime 370718366209 := by
  apply lucas_primality 370718366209 (17 : ZMod 370718366209)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (463, 1), (521281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (463, 1), (521281, 1)] : List FactorBlock).map factorBlockValue).prod) = 370718366209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_463
      · exact prime_thirtyFourAF_521281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 370718366209) ^ 185359183104 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 370718366209) ^ 123572788736 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 370718366209) ^ 800687616 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 370718366209) ^ 711168 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_374230418579 : Nat.Prime 374230418579 := by
  apply lucas_primality 374230418579 (2 : ZMod 374230418579)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (11006777017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (11006777017, 1)] : List FactorBlock).map factorBlockValue).prod) = 374230418579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_11006777017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 374230418579) ^ 187115209289 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 374230418579) ^ 22013554034 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 374230418579) ^ 34 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_395043748273 : Nat.Prime 395043748273 := by
  apply lucas_primality 395043748273 (5 : ZMod 395043748273)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (1871, 1), (162917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (1871, 1), (162917, 1)] : List FactorBlock).map factorBlockValue).prod) = 395043748273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_1871
      · exact prime_thirtyFourAF_162917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 395043748273) ^ 197521874136 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 131681249424 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 211140432 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 2424816 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_403573002901 : Nat.Prime 403573002901 := by
  apply lucas_primality 403573002901 (2 : ZMod 403573002901)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (23, 1), (73, 1), (801217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (23, 1), (73, 1), (801217, 1)] : List FactorBlock).map factorBlockValue).prod) = 403573002901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_73
      · exact prime_thirtyFourAF_801217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 403573002901) ^ 201786501450 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 403573002901) ^ 134524334300 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 403573002901) ^ 80714600580 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 403573002901) ^ 17546652300 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 403573002901) ^ 5528397300 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 403573002901) ^ 503700 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_435674924099 : Nat.Prime 435674924099 := by
  apply lucas_primality 435674924099 (2 : ZMod 435674924099)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (599, 1), (739, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (599, 1), (739, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod) = 435674924099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_151
      · exact prime_thirtyFourAF_599
      · exact prime_thirtyFourAF_739
      · exact prime_thirtyFourAF_3259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435674924099) ^ 217837462049 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 2885264398 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 727337102 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 589546582 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 133683622 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_447477687071 : Nat.Prime 447477687071 := by
  apply lucas_primality 447477687071 (19 : ZMod 447477687071)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (44747768707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (44747768707, 1)] : List FactorBlock).map factorBlockValue).prod) = 447477687071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_44747768707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 447477687071) ^ 223738843535 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (19 : ZMod 447477687071) ^ 89495537414 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (19 : ZMod 447477687071) ^ 10 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_397
      · exact prime_thirtyFourAF_2531
      · exact prime_thirtyFourAF_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_504121961207 : Nat.Prime 504121961207 := by
  apply lucas_primality 504121961207 (5 : ZMod 504121961207)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (277, 1), (461, 1), (32359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (277, 1), (461, 1), (32359, 1)] : List FactorBlock).map factorBlockValue).prod) = 504121961207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_61
      · exact prime_thirtyFourAF_277
      · exact prime_thirtyFourAF_461
      · exact prime_thirtyFourAF_32359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 504121961207) ^ 252060980603 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 8264294446 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 1819934878 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 1093540046 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 15579034 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_536509541123 : Nat.Prime 536509541123 := by
  apply lucas_primality 536509541123 (2 : ZMod 536509541123)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (268254770561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (268254770561, 1)] : List FactorBlock).map factorBlockValue).prod) = 536509541123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_268254770561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 536509541123) ^ 268254770561 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 536509541123) ^ 2 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_563223568793 : Nat.Prime 563223568793 := by
  apply lucas_primality 563223568793 (3 : ZMod 563223568793)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (227, 1), (271, 1), (30931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (227, 1), (271, 1), (30931, 1)] : List FactorBlock).map factorBlockValue).prod) = 563223568793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_227
      · exact prime_thirtyFourAF_271
      · exact prime_thirtyFourAF_30931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 563223568793) ^ 281611784396 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 15222258616 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 2481161096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 2078315752 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 18209032 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_636949592813 : Nat.Prime 636949592813 := by
  apply lucas_primality 636949592813 (2 : ZMod 636949592813)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (47, 1), (101, 1), (479, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (47, 1), (101, 1), (479, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) = 636949592813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_479
      · exact prime_thirtyFourAF_5387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 636949592813) ^ 318474796406 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 636949592813) ^ 48996122524 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 636949592813) ^ 13552118996 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 636949592813) ^ 6306431612 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 636949592813) ^ 1329748628 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 636949592813) ^ 118238276 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_648828204719 : Nat.Prime 648828204719 := by
  apply lucas_primality 648828204719 (7 : ZMod 648828204719)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41983, 1), (7727273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41983, 1), (7727273, 1)] : List FactorBlock).map factorBlockValue).prod) = 648828204719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_41983
      · exact prime_thirtyFourAF_7727273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 648828204719) ^ 324414102359 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 648828204719) ^ 15454546 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 648828204719) ^ 83966 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_670346901547 : Nat.Prime 670346901547 := by
  apply lucas_primality 670346901547 (2 : ZMod 670346901547)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (10211, 1), (1563083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (10211, 1), (1563083, 1)] : List FactorBlock).map factorBlockValue).prod) = 670346901547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_10211
      · exact prime_thirtyFourAF_1563083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 670346901547) ^ 335173450773 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 223448967182 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 95763843078 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 65649486 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 428862 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1404606769961 : Nat.Prime 1404606769961 := by
  apply lucas_primality 1404606769961 (3 : ZMod 1404606769961)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (816631843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (816631843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1404606769961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_816631843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1404606769961) ^ 702303384980 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1404606769961) ^ 280921353992 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1404606769961) ^ 32665273720 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1404606769961) ^ 1720 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1418482166971 : Nat.Prime 1418482166971 := by
  apply lucas_primality 1418482166971 (3 : ZMod 1418482166971)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (71, 1), (83, 1), (729413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (71, 1), (83, 1), (729413, 1)] : List FactorBlock).map factorBlockValue).prod) = 1418482166971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_71
      · exact prime_thirtyFourAF_83
      · exact prime_thirtyFourAF_729413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1418482166971) ^ 709241083485 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418482166971) ^ 472827388990 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418482166971) ^ 283696433394 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418482166971) ^ 128952924270 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418482166971) ^ 19978622070 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418482166971) ^ 17090146590 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418482166971) ^ 1944690 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1433190624797 : Nat.Prime 1433190624797 := by
  apply lucas_primality 1433190624797 (2 : ZMod 1433190624797)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (126641, 1), (404177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (126641, 1), (404177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1433190624797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_126641
      · exact prime_thirtyFourAF_404177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1433190624797) ^ 716595312398 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433190624797) ^ 204741517828 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433190624797) ^ 11316956 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433190624797) ^ 3545948 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_35279
      · exact prime_thirtyFourAF_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1830410902139 : Nat.Prime 1830410902139 := by
  apply lucas_primality 1830410902139 (2 : ZMod 1830410902139)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (19, 1), (529326461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (19, 1), (529326461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1830410902139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_529326461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1830410902139) ^ 915205451069 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830410902139) ^ 261487271734 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830410902139) ^ 140800838626 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830410902139) ^ 96337415902 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830410902139) ^ 3458 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2065025594587 : Nat.Prime 2065025594587 := by
  apply lucas_primality 2065025594587 (3 : ZMod 2065025594587)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (344170932431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (344170932431, 1)] : List FactorBlock).map factorBlockValue).prod) = 2065025594587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_344170932431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2065025594587) ^ 1032512797293 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065025594587) ^ 688341864862 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065025594587) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2085352522321 : Nat.Prime 2085352522321 := by
  apply lucas_primality 2085352522321 (14 : ZMod 2085352522321)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (467, 1), (653, 1), (28493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (467, 1), (653, 1), (28493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2085352522321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_467
      · exact prime_thirtyFourAF_653
      · exact prime_thirtyFourAF_28493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2085352522321) ^ 1042676261160 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 2085352522321) ^ 695117507440 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 2085352522321) ^ 417070504464 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 2085352522321) ^ 4465422960 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 2085352522321) ^ 3193495440 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 2085352522321) ^ 73188240 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2374672997579 : Nat.Prime 2374672997579 := by
  apply lucas_primality 2374672997579 (2 : ZMod 2374672997579)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (169619499827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (169619499827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2374672997579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_169619499827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2374672997579) ^ 1187336498789 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2374672997579) ^ 339238999654 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2374672997579) ^ 14 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2531202436621 : Nat.Prime 2531202436621 := by
  apply lucas_primality 2531202436621 (10 : ZMod 2531202436621)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (13, 1), (53, 1), (1855421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (13, 1), (53, 1), (1855421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2531202436621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_1855421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2531202436621) ^ 1265601218310 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2531202436621) ^ 843734145540 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2531202436621) ^ 506240487324 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2531202436621) ^ 230109312420 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2531202436621) ^ 194707879740 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2531202436621) ^ 47758536540 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2531202436621) ^ 1364220 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2631286828661 : Nat.Prime 2631286828661 := by
  apply lucas_primality 2631286828661 (3 : ZMod 2631286828661)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (18794905919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (18794905919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2631286828661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_18794905919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2631286828661) ^ 1315643414330 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631286828661) ^ 526257365732 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631286828661) ^ 375898118380 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631286828661) ^ 140 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3033740920883 : Nat.Prime 3033740920883 := by
  apply lucas_primality 3033740920883 (2 : ZMod 3033740920883)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (197, 1), (157139797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (197, 1), (157139797, 1)] : List FactorBlock).map factorBlockValue).prod) = 3033740920883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_197
      · exact prime_thirtyFourAF_157139797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3033740920883) ^ 1516870460441 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3033740920883) ^ 433391560126 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3033740920883) ^ 15399700106 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3033740920883) ^ 19306 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_6126952389931 : Nat.Prime 6126952389931 := by
  apply lucas_primality 6126952389931 (2 : ZMod 6126952389931)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (113, 1), (5657, 1), (11833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (113, 1), (5657, 1), (11833, 1)] : List FactorBlock).map factorBlockValue).prod) = 6126952389931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_113
      · exact prime_thirtyFourAF_5657
      · exact prime_thirtyFourAF_11833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6126952389931) ^ 3063476194965 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 2042317463310 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 1225390477986 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 54220817610 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 1083074490 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 517785210 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_6768253648501 : Nat.Prime 6768253648501 := by
  apply lucas_primality 6768253648501 (2 : ZMod 6768253648501)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (607, 1), (2459, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (607, 1), (2459, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) = 6768253648501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_607
      · exact prime_thirtyFourAF_2459
      · exact prime_thirtyFourAF_3023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6768253648501) ^ 3384126824250 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6768253648501) ^ 2256084549500 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6768253648501) ^ 1353650729700 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6768253648501) ^ 11150335500 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6768253648501) ^ 2752441500 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6768253648501) ^ 2238919500 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_7244372988773 : Nat.Prime 7244372988773 := by
  apply lucas_primality 7244372988773 (2 : ZMod 7244372988773)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (6886286111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (6886286111, 1)] : List FactorBlock).map factorBlockValue).prod) = 7244372988773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_263
      · exact prime_thirtyFourAF_6886286111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7244372988773) ^ 3622186494386 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244372988773) ^ 27545144444 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244372988773) ^ 1052 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_7908989265053 : Nat.Prime 7908989265053 := by
  apply lucas_primality 7908989265053 (2 : ZMod 7908989265053)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (6397, 1), (1850837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (6397, 1), (1850837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7908989265053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_167
      · exact prime_thirtyFourAF_6397
      · exact prime_thirtyFourAF_1850837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7908989265053) ^ 3954494632526 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 47359217156 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 1236359116 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 4273196 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_8235844998163 : Nat.Prime 8235844998163 := by
  apply lucas_primality 8235844998163 (2 : ZMod 8235844998163)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (514309, 1), (2668903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (514309, 1), (2668903, 1)] : List FactorBlock).map factorBlockValue).prod) = 8235844998163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_514309
      · exact prime_thirtyFourAF_2668903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8235844998163) ^ 4117922499081 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8235844998163) ^ 2745281666054 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8235844998163) ^ 16013418 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8235844998163) ^ 3085854 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_9956099729759 : Nat.Prime 9956099729759 := by
  apply lucas_primality 9956099729759 (7 : ZMod 9956099729759)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (54703844669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (54703844669, 1)] : List FactorBlock).map factorBlockValue).prod) = 9956099729759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_54703844669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9956099729759) ^ 4978049864879 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 9956099729759) ^ 1422299961394 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 9956099729759) ^ 765853825366 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 9956099729759) ^ 182 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_10359237208517 : Nat.Prime 10359237208517 := by
  apply lucas_primality 10359237208517 (2 : ZMod 10359237208517)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3917, 1), (94453091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3917, 1), (94453091, 1)] : List FactorBlock).map factorBlockValue).prod) = 10359237208517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_3917
      · exact prime_thirtyFourAF_94453091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10359237208517) ^ 5179618604258 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10359237208517) ^ 1479891029788 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10359237208517) ^ 2644686548 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10359237208517) ^ 109676 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_11492716013243 : Nat.Prime 11492716013243 := by
  apply lucas_primality 11492716013243 (2 : ZMod 11492716013243)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (338021059213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (338021059213, 1)] : List FactorBlock).map factorBlockValue).prod) = 11492716013243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_338021059213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11492716013243) ^ 5746358006621 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11492716013243) ^ 676042118426 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11492716013243) ^ 34 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_13424330612131 : Nat.Prime 13424330612131 := by
  apply lucas_primality 13424330612131 (2 : ZMod 13424330612131)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (447477687071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (447477687071, 1)] : List FactorBlock).map factorBlockValue).prod) = 13424330612131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_447477687071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13424330612131) ^ 6712165306065 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13424330612131) ^ 4474776870710 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13424330612131) ^ 2684866122426 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13424330612131) ^ 30 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_15739574530651 : Nat.Prime 15739574530651 := by
  apply lucas_primality 15739574530651 (2 : ZMod 15739574530651)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (199, 1), (2939, 1), (179411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (199, 1), (2939, 1), (179411, 1)] : List FactorBlock).map factorBlockValue).prod) = 15739574530651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_199
      · exact prime_thirtyFourAF_2939
      · exact prime_thirtyFourAF_179411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15739574530651) ^ 7869787265325 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15739574530651) ^ 5246524843550 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15739574530651) ^ 3147914906130 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15739574530651) ^ 79093339350 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15739574530651) ^ 5355418350 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15739574530651) ^ 87729150 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_18076669791347 : Nat.Prime 18076669791347 := by
  apply lucas_primality 18076669791347 (2 : ZMod 18076669791347)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (5653, 1), (3033883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (5653, 1), (3033883, 1)] : List FactorBlock).map factorBlockValue).prod) = 18076669791347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_5653
      · exact prime_thirtyFourAF_3033883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18076669791347) ^ 9038334895673 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 1063333517138 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 583118380366 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 3197712682 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 5958262 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_18107153021773 : Nat.Prime 18107153021773 := by
  apply lucas_primality 18107153021773 (2 : ZMod 18107153021773)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (89, 1), (28547, 1), (197969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (89, 1), (28547, 1), (197969, 1)] : List FactorBlock).map factorBlockValue).prod) = 18107153021773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_89
      · exact prime_thirtyFourAF_28547
      · exact prime_thirtyFourAF_197969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18107153021773) ^ 9053576510886 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 6035717673924 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 203451157548 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 634292676 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 91464588 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_20710593337979 : Nat.Prime 20710593337979 := by
  apply lucas_primality 20710593337979 (2 : ZMod 20710593337979)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (145849248859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (145849248859, 1)] : List FactorBlock).map factorBlockValue).prod) = 20710593337979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_71
      · exact prime_thirtyFourAF_145849248859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20710593337979) ^ 10355296668989 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 20710593337979) ^ 291698497718 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 20710593337979) ^ 142 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_66451830061937 : Nat.Prime 66451830061937 := by
  apply lucas_primality 66451830061937 (3 : ZMod 66451830061937)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (572791, 1), (659171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (572791, 1), (659171, 1)] : List FactorBlock).map factorBlockValue).prod) = 66451830061937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_572791
      · exact prime_thirtyFourAF_659171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66451830061937) ^ 33225915030968 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 6041075460176 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 116014096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 100811216 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_83685839216201 : Nat.Prime 83685839216201 := by
  apply lucas_primality 83685839216201 (3 : ZMod 83685839216201)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (32186861237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (32186861237, 1)] : List FactorBlock).map factorBlockValue).prod) = 83685839216201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_32186861237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 83685839216201) ^ 41842919608100 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 83685839216201) ^ 16737167843240 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 83685839216201) ^ 6437372247400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 83685839216201) ^ 2600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_106619097506671 : Nat.Prime 106619097506671 := by
  apply lucas_primality 106619097506671 (12 : ZMod 106619097506671)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (199, 1), (7661581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (199, 1), (7661581, 1)] : List FactorBlock).map factorBlockValue).prod) = 106619097506671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_199
      · exact prime_thirtyFourAF_7661581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 106619097506671) ^ 53309548753335 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 35539699168890 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 21323819501334 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 15231299643810 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 2881597229910 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 535774359330 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 13916070 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_110514046803763 : Nat.Prime 110514046803763 := by
  apply lucas_primality 110514046803763 (2 : ZMod 110514046803763)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2631286828661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2631286828661, 1)] : List FactorBlock).map factorBlockValue).prod) = 110514046803763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_2631286828661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110514046803763) ^ 55257023401881 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110514046803763) ^ 36838015601254 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110514046803763) ^ 15787720971966 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110514046803763) ^ 42 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_129876803368223 : Nat.Prime 129876803368223 := by
  apply lucas_primality 129876803368223 (5 : ZMod 129876803368223)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (7529, 1), (109178521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (7529, 1), (109178521, 1)] : List FactorBlock).map factorBlockValue).prod) = 129876803368223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_79
      · exact prime_thirtyFourAF_7529
      · exact prime_thirtyFourAF_109178521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129876803368223) ^ 64938401684111 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 1644010169218 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 17250206318 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 1189582 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_140896947156781 : Nat.Prime 140896947156781 := by
  apply lucas_primality 140896947156781 (6 : ZMod 140896947156781)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (101, 1), (419, 1), (55490027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (101, 1), (419, 1), (55490027, 1)] : List FactorBlock).map factorBlockValue).prod) = 140896947156781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_419
      · exact prime_thirtyFourAF_55490027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140896947156781) ^ 70448473578390 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 46965649052260 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 28179389431356 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 1395019278780 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 336269563620 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 2539140 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_228014296889441 : Nat.Prime 228014296889441 := by
  apply lucas_primality 228014296889441 (3 : ZMod 228014296889441)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (149, 1), (9564358091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (149, 1), (9564358091, 1)] : List FactorBlock).map factorBlockValue).prod) = 228014296889441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_149
      · exact prime_thirtyFourAF_9564358091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 228014296889441) ^ 114007148444720 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 45602859377888 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 1530297294560 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 23840 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_341422760454247 : Nat.Prime 341422760454247 := by
  apply lucas_primality 341422760454247 (3 : ZMod 341422760454247)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (403573002901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (403573002901, 1)] : List FactorBlock).map factorBlockValue).prod) = 341422760454247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_403573002901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 341422760454247) ^ 170711380227123 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 341422760454247) ^ 113807586818082 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 341422760454247) ^ 7264314052218 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 341422760454247) ^ 846 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_392262443383511 : Nat.Prime 392262443383511 := by
  apply lucas_primality 392262443383511 (7 : ZMod 392262443383511)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (163561, 1), (34260913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (163561, 1), (34260913, 1)] : List FactorBlock).map factorBlockValue).prod) = 392262443383511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_163561
      · exact prime_thirtyFourAF_34260913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 392262443383511) ^ 196131221691755 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 392262443383511) ^ 78452488676702 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 392262443383511) ^ 56037491911930 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 392262443383511) ^ 2398263910 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 392262443383511) ^ 11449270 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_468249070338449 : Nat.Prime 468249070338449 := by
  apply lucas_primality 468249070338449 (3 : ZMod 468249070338449)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (347, 1), (12048401357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (347, 1), (12048401357, 1)] : List FactorBlock).map factorBlockValue).prod) = 468249070338449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_347
      · exact prime_thirtyFourAF_12048401357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 468249070338449) ^ 234124535169224 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 66892724334064 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 1349420951984 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 38864 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_539238927990449 : Nat.Prime 539238927990449 := by
  apply lucas_primality 539238927990449 (3 : ZMod 539238927990449)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (571, 1), (8431932199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (571, 1), (8431932199, 1)] : List FactorBlock).map factorBlockValue).prod) = 539238927990449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_571
      · exact prime_thirtyFourAF_8431932199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 539238927990449) ^ 269619463995224 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 539238927990449) ^ 77034132570064 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 539238927990449) ^ 944376406288 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 539238927990449) ^ 63952 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_540658350927197 : Nat.Prime 540658350927197 := by
  apply lucas_primality 540658350927197 (2 : ZMod 540658350927197)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (159421, 1), (847846819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (159421, 1), (847846819, 1)] : List FactorBlock).map factorBlockValue).prod) = 540658350927197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_159421
      · exact prime_thirtyFourAF_847846819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 540658350927197) ^ 270329175463598 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 540658350927197) ^ 3391387276 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 540658350927197) ^ 637684 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_754643424782869 : Nat.Prime 754643424782869 := by
  apply lucas_primality 754643424782869 (7 : ZMod 754643424782869)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (853, 1), (3880233977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (853, 1), (3880233977, 1)] : List FactorBlock).map factorBlockValue).prod) = 754643424782869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_853
      · exact prime_thirtyFourAF_3880233977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 754643424782869) ^ 377321712391434 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 251547808260956 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 39718074988572 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 884693346756 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 194484 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_914619143007077 : Nat.Prime 914619143007077 := by
  apply lucas_primality 914619143007077 (2 : ZMod 914619143007077)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (47, 1), (374230418579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (47, 1), (374230418579, 1)] : List FactorBlock).map factorBlockValue).prod) = 914619143007077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_374230418579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 914619143007077) ^ 457309571503538 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914619143007077) ^ 70355318692852 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914619143007077) ^ 19459981766108 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914619143007077) ^ 2444 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1244262030860441 : Nat.Prime 1244262030860441 := by
  apply lucas_primality 1244262030860441 (3 : ZMod 1244262030860441)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (117361, 1), (6163957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (117361, 1), (6163957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244262030860441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_117361
      · exact prime_thirtyFourAF_6163957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1244262030860441) ^ 622131015430220 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244262030860441) ^ 248852406172088 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244262030860441) ^ 28936326299080 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244262030860441) ^ 10602006040 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1244262030860441) ^ 201860920 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1521412008583583 : Nat.Prime 1521412008583583 := by
  apply lucas_primality 1521412008583583 (5 : ZMod 1521412008583583)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20431, 1), (110069, 1), (338269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20431, 1), (110069, 1), (338269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521412008583583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_20431
      · exact prime_thirtyFourAF_110069
      · exact prime_thirtyFourAF_338269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1521412008583583) ^ 760706004291791 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1521412008583583) ^ 74465861122 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1521412008583583) ^ 13822347878 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1521412008583583) ^ 4497639478 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2733798320613229 : Nat.Prime 2733798320613229 := by
  apply lucas_primality 2733798320613229 (2 : ZMod 2733798320613229)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (20710593337979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (20710593337979, 1)] : List FactorBlock).map factorBlockValue).prod) = 2733798320613229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_20710593337979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2733798320613229) ^ 1366899160306614 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733798320613229) ^ 911266106871076 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733798320613229) ^ 248527120055748 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733798320613229) ^ 132 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_8404644125874427 : Nat.Prime 8404644125874427 := by
  apply lucas_primality 8404644125874427 (2 : ZMod 8404644125874427)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257, 1), (3559, 1), (1531464617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257, 1), (3559, 1), (1531464617, 1)] : List FactorBlock).map factorBlockValue).prod) = 8404644125874427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_257
      · exact prime_thirtyFourAF_3559
      · exact prime_thirtyFourAF_1531464617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8404644125874427) ^ 4202322062937213 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 2801548041958142 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 32702895431418 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 2361518439414 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 5487978 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_12772601740670833 : Nat.Prime 12772601740670833 := by
  apply lucas_primality 12772601740670833 (5 : ZMod 12772601740670833)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (3121, 1), (3229, 1), (8801467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (3121, 1), (3229, 1), (8801467, 1)] : List FactorBlock).map factorBlockValue).prod) = 12772601740670833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_3121
      · exact prime_thirtyFourAF_3229
      · exact prime_thirtyFourAF_8801467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12772601740670833) ^ 6386300870335416 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12772601740670833) ^ 4257533913556944 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12772601740670833) ^ 4092470919792 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12772601740670833) ^ 3955590505008 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12772601740670833) ^ 1451190096 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_40474501653905201 : Nat.Prime 40474501653905201 := by
  apply lucas_primality 40474501653905201 (3 : ZMod 40474501653905201)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 2), (2065025594587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 2), (2065025594587, 1)] : List FactorBlock).map factorBlockValue).prod) = 40474501653905201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_2065025594587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40474501653905201) ^ 20237250826952600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40474501653905201) ^ 8094900330781040 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40474501653905201) ^ 5782071664843600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40474501653905201) ^ 19600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_58245344094475897 : Nat.Prime 58245344094475897 := by
  apply lucas_primality 58245344094475897 (5 : ZMod 58245344094475897)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (83685839216201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (83685839216201, 1)] : List FactorBlock).map factorBlockValue).prod) = 58245344094475897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_83685839216201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58245344094475897) ^ 29122672047237948 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 58245344094475897) ^ 19415114698158632 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 58245344094475897) ^ 2008460141188824 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 58245344094475897) ^ 696 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_76546352977170413 : Nat.Prime 76546352977170413 := by
  apply lucas_primality 76546352977170413 (2 : ZMod 76546352977170413)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2733798320613229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2733798320613229, 1)] : List FactorBlock).map factorBlockValue).prod) = 76546352977170413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_2733798320613229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76546352977170413) ^ 38273176488585206 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 76546352977170413) ^ 10935193282452916 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 76546352977170413) ^ 28 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_90889077331232519 : Nat.Prime 90889077331232519 := by
  apply lucas_primality 90889077331232519 (11 : ZMod 90889077331232519)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (851549, 1), (4105146907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (851549, 1), (4105146907, 1)] : List FactorBlock).map factorBlockValue).prod) = 90889077331232519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_851549
      · exact prime_thirtyFourAF_4105146907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 90889077331232519) ^ 45444538665616259 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 90889077331232519) ^ 6991467487017886 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 90889077331232519) ^ 106733819582 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 90889077331232519) ^ 22140274 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_102223266935858869 : Nat.Prime 102223266935858869 := by
  apply lucas_primality 102223266935858869 (2 : ZMod 102223266935858869)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (61, 1), (627481, 1), (11713441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (61, 1), (627481, 1), (11713441, 1)] : List FactorBlock).map factorBlockValue).prod) = 102223266935858869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_61
      · exact prime_thirtyFourAF_627481
      · exact prime_thirtyFourAF_11713441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102223266935858869) ^ 51111633467929434 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 34074422311952956 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 5380171943992572 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 1675791261243588 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 162910537428 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 8727005748 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_113814267595358257 : Nat.Prime 113814267595358257 := by
  apply lucas_primality 113814267595358257 (5 : ZMod 113814267595358257)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (43, 1), (6126952389931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (43, 1), (6126952389931, 1)] : List FactorBlock).map factorBlockValue).prod) = 113814267595358257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_6126952389931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 113814267595358257) ^ 56907133797679128 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 37938089198452752 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 2646843432450192 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 18576 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_148047202981516331 : Nat.Prime 148047202981516331 := by
  apply lucas_primality 148047202981516331 (6 : ZMod 148047202981516331)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1487, 1), (9956099729759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1487, 1), (9956099729759, 1)] : List FactorBlock).map factorBlockValue).prod) = 148047202981516331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_1487
      · exact prime_thirtyFourAF_9956099729759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 148047202981516331) ^ 74023601490758165 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 148047202981516331) ^ 29609440596303266 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 148047202981516331) ^ 99560997297590 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 148047202981516331) ^ 14870 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_267582603990315871 : Nat.Prime 267582603990315871 := by
  apply lucas_primality 267582603990315871 (11 : ZMod 267582603990315871)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 2), (8235844998163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 2), (8235844998163, 1)] : List FactorBlock).map factorBlockValue).prod) = 267582603990315871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_8235844998163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 267582603990315871) ^ 133791301995157935 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 267582603990315871) ^ 89194201330105290 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 267582603990315871) ^ 53516520798063174 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 267582603990315871) ^ 14083294946858730 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 267582603990315871) ^ 32490 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_382018399699385413 : Nat.Prime 382018399699385413 := by
  apply lucas_primality 382018399699385413 (2 : ZMod 382018399699385413)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (347, 1), (536509541123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (347, 1), (536509541123, 1)] : List FactorBlock).map factorBlockValue).prod) = 382018399699385413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_347
      · exact prime_thirtyFourAF_536509541123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 382018399699385413) ^ 191009199849692706 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 127339466566461804 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 20106231563125548 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 1100917578384396 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 712044 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_504051854825488309 : Nat.Prime 504051854825488309 := by
  apply lucas_primality 504051854825488309 (13 : ZMod 504051854825488309)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (277, 1), (49417, 1), (133416637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (277, 1), (49417, 1), (133416637, 1)] : List FactorBlock).map factorBlockValue).prod) = 504051854825488309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_277
      · exact prime_thirtyFourAF_49417
      · exact prime_thirtyFourAF_133416637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 504051854825488309) ^ 252025927412744154 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 168017284941829436 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 21915298035890796 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 1819681786373604 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 10199968731924 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 3778028484 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_61717
      · exact prime_thirtyFourAF_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_598240516789697927 : Nat.Prime 598240516789697927 := by
  apply lucas_primality 598240516789697927 (5 : ZMod 598240516789697927)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163417, 1), (1830410902139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163417, 1), (1830410902139, 1)] : List FactorBlock).map factorBlockValue).prod) = 598240516789697927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_163417
      · exact prime_thirtyFourAF_1830410902139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 598240516789697927) ^ 299120258394848963 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 598240516789697927) ^ 3660821804278 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 598240516789697927) ^ 326834 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_658410660431626873 : Nat.Prime 658410660431626873 := by
  apply lucas_primality 658410660431626873 (17 : ZMod 658410660431626873)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (293, 1), (661, 1), (1839610193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (293, 1), (661, 1), (1839610193, 1)] : List FactorBlock).map factorBlockValue).prod) = 658410660431626873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_293
      · exact prime_thirtyFourAF_661
      · exact prime_thirtyFourAF_1839610193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 658410660431626873) ^ 329205330215813436 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 658410660431626873) ^ 219470220143875624 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 658410660431626873) ^ 94058665775946696 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 658410660431626873) ^ 59855514584693352 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 658410660431626873) ^ 2247135359834904 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 658410660431626873) ^ 996082693542552 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 658410660431626873) ^ 357907704 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_682885605572149543 : Nat.Prime 682885605572149543 := by
  apply lucas_primality 682885605572149543 (3 : ZMod 682885605572149543)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113814267595358257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113814267595358257, 1)] : List FactorBlock).map factorBlockValue).prod) = 682885605572149543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_113814267595358257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 682885605572149543) ^ 341442802786074771 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 682885605572149543) ^ 227628535190716514 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 682885605572149543) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1256630274186794203 : Nat.Prime 1256630274186794203 := by
  apply lucas_primality 1256630274186794203 (2 : ZMod 1256630274186794203)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17562977, 1), (11924993071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17562977, 1), (11924993071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1256630274186794203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_17562977
      · exact prime_thirtyFourAF_11924993071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1256630274186794203) ^ 628315137093397101 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1256630274186794203) ^ 418876758062264734 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1256630274186794203) ^ 71549958426 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1256630274186794203) ^ 105377862 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2809972382947583261 : Nat.Prime 2809972382947583261 := by
  apply lucas_primality 2809972382947583261 (2 : ZMod 2809972382947583261)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (12772601740670833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (12772601740670833, 1)] : List FactorBlock).map factorBlockValue).prod) = 2809972382947583261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_12772601740670833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2809972382947583261) ^ 1404986191473791630 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2809972382947583261) ^ 561994476589516652 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2809972382947583261) ^ 255452034813416660 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2809972382947583261) ^ 220 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3379627908495294503 : Nat.Prime 3379627908495294503 := by
  apply lucas_primality 3379627908495294503 (5 : ZMod 3379627908495294503)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7411, 1), (228014296889441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7411, 1), (228014296889441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3379627908495294503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7411
      · exact prime_thirtyFourAF_228014296889441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3379627908495294503) ^ 1689813954247647251 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3379627908495294503) ^ 456028593778882 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3379627908495294503) ^ 14822 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_6533831533403812223 : Nat.Prime 6533831533403812223 := by
  apply lucas_primality 6533831533403812223 (5 : ZMod 6533831533403812223)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2357, 1), (106619097506671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2357, 1), (106619097506671, 1)] : List FactorBlock).map factorBlockValue).prod) = 6533831533403812223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_2357
      · exact prime_thirtyFourAF_106619097506671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6533831533403812223) ^ 3266915766701906111 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 502602425646447094 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 2772096535173446 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 61282 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_439
      · exact prime_thirtyFourAF_853
      · exact prime_thirtyFourAF_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_9866150589381930971 : Nat.Prime 9866150589381930971 := by
  apply lucas_primality 9866150589381930971 (6 : ZMod 9866150589381930971)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (251, 1), (997, 1), (563223568793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (251, 1), (997, 1), (563223568793, 1)] : List FactorBlock).map factorBlockValue).prod) = 9866150589381930971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_251
      · exact prime_thirtyFourAF_997
      · exact prime_thirtyFourAF_563223568793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9866150589381930971) ^ 4933075294690965485 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 1973230117876386194 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 1409450084197418710 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 39307372866063470 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 9895838103693010 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 17517290 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_22921103981963124781 : Nat.Prime 22921103981963124781 := by
  apply lucas_primality 22921103981963124781 (2 : ZMod 22921103981963124781)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (382018399699385413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (382018399699385413, 1)] : List FactorBlock).map factorBlockValue).prod) = 22921103981963124781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_382018399699385413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22921103981963124781) ^ 11460551990981562390 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22921103981963124781) ^ 7640367993987708260 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22921103981963124781) ^ 4584220796392624956 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22921103981963124781) ^ 60 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_31255574362747278433 : Nat.Prime 31255574362747278433 := by
  apply lucas_primality 31255574362747278433 (5 : ZMod 31255574362747278433)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (31, 1), (83, 1), (18076669791347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (31, 1), (83, 1), (18076669791347, 1)] : List FactorBlock).map factorBlockValue).prod) = 31255574362747278433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_83
      · exact prime_thirtyFourAF_18076669791347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31255574362747278433) ^ 15627787181373639216 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 10418524787582426144 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 4465082051821039776 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 1008244334282170272 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 376573185093340704 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 1729056 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_47004755940671233151 : Nat.Prime 47004755940671233151 := by
  apply lucas_primality 47004755940671233151 (17 : ZMod 47004755940671233151)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (3779, 1), (6287, 1), (39568669331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (3779, 1), (6287, 1), (39568669331, 1)] : List FactorBlock).map factorBlockValue).prod) = 47004755940671233151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_3779
      · exact prime_thirtyFourAF_6287
      · exact prime_thirtyFourAF_39568669331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 47004755940671233151) ^ 23502377970335616575 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 9400951188134246630 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 12438411204199850 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 7476500070092450 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 1187928650 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_67519358359994571007 : Nat.Prime 67519358359994571007 := by
  apply lucas_primality 67519358359994571007 (3 : ZMod 67519358359994571007)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2503, 1), (21073271, 1), (213345877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2503, 1), (21073271, 1), (213345877, 1)] : List FactorBlock).map factorBlockValue).prod) = 67519358359994571007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_2503
      · exact prime_thirtyFourAF_21073271
      · exact prime_thirtyFourAF_213345877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67519358359994571007) ^ 33759679179997285503 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67519358359994571007) ^ 22506452786664857002 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67519358359994571007) ^ 26975372896522002 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67519358359994571007) ^ 3204028380786 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67519358359994571007) ^ 316478383878 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_69924730862683817723 : Nat.Prime 69924730862683817723 := by
  apply lucas_primality 69924730862683817723 (2 : ZMod 69924730862683817723)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 5), (6101, 1), (340964828623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 5), (6101, 1), (340964828623, 1)] : List FactorBlock).map factorBlockValue).prod) = 69924730862683817723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_6101
      · exact prime_thirtyFourAF_340964828623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69924730862683817723) ^ 34962365431341908861 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 69924730862683817723) ^ 9989247266097688246 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 69924730862683817723) ^ 11461191749333522 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 69924730862683817723) ^ 205079014 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_85992210770920657639 : Nat.Prime 85992210770920657639 := by
  apply lucas_primality 85992210770920657639 (3 : ZMod 85992210770920657639)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (677, 1), (129876803368223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (677, 1), (129876803368223, 1)] : List FactorBlock).map factorBlockValue).prod) = 85992210770920657639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_163
      · exact prime_thirtyFourAF_677
      · exact prime_thirtyFourAF_129876803368223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85992210770920657639) ^ 42996105385460328819 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 28664070256973552546 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 527559575281721826 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 127019513694122094 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 662106 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_126839061027076803557 : Nat.Prime 126839061027076803557 := by
  apply lucas_primality 126839061027076803557 (2 : ZMod 126839061027076803557)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (100602899, 1), (1376407559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (100602899, 1), (1376407559, 1)] : List FactorBlock).map factorBlockValue).prod) = 126839061027076803557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_229
      · exact prime_thirtyFourAF_100602899
      · exact prime_thirtyFourAF_1376407559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126839061027076803557) ^ 63419530513538401778 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126839061027076803557) ^ 553882362563654164 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126839061027076803557) ^ 1260789324044 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126839061027076803557) ^ 92152255484 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_137526623891778748687 : Nat.Prime 137526623891778748687 := by
  apply lucas_primality 137526623891778748687 (3 : ZMod 137526623891778748687)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22921103981963124781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22921103981963124781, 1)] : List FactorBlock).map factorBlockValue).prod) = 137526623891778748687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_22921103981963124781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 137526623891778748687) ^ 68763311945889374343 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 137526623891778748687) ^ 45842207963926249562 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 137526623891778748687) ^ 6 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_167656698254789693023 : Nat.Prime 167656698254789693023 := by
  apply lucas_primality 167656698254789693023 (3 : ZMod 167656698254789693023)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (75374693, 1), (370718366209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (75374693, 1), (370718366209, 1)] : List FactorBlock).map factorBlockValue).prod) = 167656698254789693023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_75374693
      · exact prime_thirtyFourAF_370718366209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 167656698254789693023) ^ 83828349127394846511 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 167656698254789693023) ^ 55885566084929897674 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 167656698254789693023) ^ 2224310197254 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 167656698254789693023) ^ 452248158 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_179342389870853805599 : Nat.Prime 179342389870853805599 := by
  apply lucas_primality 179342389870853805599 (11 : ZMod 179342389870853805599)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (136601, 1), (7908989265053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (136601, 1), (7908989265053, 1)] : List FactorBlock).map factorBlockValue).prod) = 179342389870853805599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_83
      · exact prime_thirtyFourAF_136601
      · exact prime_thirtyFourAF_7908989265053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 179342389870853805599) ^ 89671194935426902799 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 2160751685191009706 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 1312892217998798 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 22675766 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_246372701184547842389 : Nat.Prime 246372701184547842389 := by
  apply lucas_primality 246372701184547842389 (2 : ZMod 246372701184547842389)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (281, 1), (4943, 1), (130041294599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (281, 1), (4943, 1), (130041294599, 1)] : List FactorBlock).map factorBlockValue).prod) = 246372701184547842389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_281
      · exact prime_thirtyFourAF_4943
      · exact prime_thirtyFourAF_130041294599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 246372701184547842389) ^ 123186350592273921194 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 246372701184547842389) ^ 22397518289504349308 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 246372701184547842389) ^ 7947506489824123948 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 246372701184547842389) ^ 876771178592696948 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 246372701184547842389) ^ 49842747559083116 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 246372701184547842389) ^ 1894572812 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_296020343906680269193 : Nat.Prime 296020343906680269193 := by
  apply lucas_primality 296020343906680269193 (5 : ZMod 296020343906680269193)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (918793, 1), (13424330612131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (918793, 1), (13424330612131, 1)] : List FactorBlock).map factorBlockValue).prod) = 296020343906680269193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_918793
      · exact prime_thirtyFourAF_13424330612131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296020343906680269193) ^ 148010171953340134596 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 296020343906680269193) ^ 98673447968893423064 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 296020343906680269193) ^ 322183934691144 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 296020343906680269193) ^ 22051032 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_366752412318474857063 : Nat.Prime 366752412318474857063 := by
  apply lucas_primality 366752412318474857063 (5 : ZMod 366752412318474857063)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (282626749, 1), (648828204719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (282626749, 1), (648828204719, 1)] : List FactorBlock).map factorBlockValue).prod) = 366752412318474857063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_282626749
      · exact prime_thirtyFourAF_648828204719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 366752412318474857063) ^ 183376206159237428531 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 366752412318474857063) ^ 1297656409438 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 366752412318474857063) ^ 565253498 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_443831096543292924709 : Nat.Prime 443831096543292924709 := by
  apply lucas_primality 443831096543292924709 (2 : ZMod 443831096543292924709)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (8511353, 1), (395043748273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (8511353, 1), (395043748273, 1)] : List FactorBlock).map factorBlockValue).prod) = 443831096543292924709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_8511353
      · exact prime_thirtyFourAF_395043748273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 443831096543292924709) ^ 221915548271646462354 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 147943698847764308236 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 40348281503935720428 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 52145774772036 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 1123498596 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_571692280977967567291 : Nat.Prime 571692280977967567291 := by
  apply lucas_primality 571692280977967567291 (10 : ZMod 571692280977967567291)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (100451987, 1), (189706644289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (100451987, 1), (189706644289, 1)] : List FactorBlock).map factorBlockValue).prod) = 571692280977967567291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_100451987
      · exact prime_thirtyFourAF_189706644289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 571692280977967567291) ^ 285846140488983783645 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 571692280977967567291) ^ 190564093659322522430 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 571692280977967567291) ^ 114338456195593513458 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 571692280977967567291) ^ 5691199328670 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 571692280977967567291) ^ 3013559610 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_627354775635530615501 : Nat.Prime 627354775635530615501 := by
  apply lucas_primality 627354775635530615501 (3 : ZMod 627354775635530615501)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (31, 1), (40474501653905201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (31, 1), (40474501653905201, 1)] : List FactorBlock).map factorBlockValue).prod) = 627354775635530615501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_40474501653905201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 627354775635530615501) ^ 313677387817765307750 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 627354775635530615501) ^ 125470955127106123100 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 627354775635530615501) ^ 20237250826952600500 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 627354775635530615501) ^ 15500 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_675193583599945710071 : Nat.Prime 675193583599945710071 := by
  apply lucas_primality 675193583599945710071 (7 : ZMod 675193583599945710071)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (67519358359994571007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (67519358359994571007, 1)] : List FactorBlock).map factorBlockValue).prod) = 675193583599945710071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_67519358359994571007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 675193583599945710071) ^ 337596791799972855035 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 675193583599945710071) ^ 135038716719989142014 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 675193583599945710071) ^ 10 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_675283202967241661693 : Nat.Prime 675283202967241661693 := by
  apply lucas_primality 675283202967241661693 (2 : ZMod 675283202967241661693)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9087309221, 1), (18577644563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9087309221, 1), (18577644563, 1)] : List FactorBlock).map factorBlockValue).prod) = 675283202967241661693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_9087309221
      · exact prime_thirtyFourAF_18577644563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 675283202967241661693) ^ 337641601483620830846 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 675283202967241661693) ^ 74310578252 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 675283202967241661693) ^ 36349236884 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1016423953159369330679 : Nat.Prime 1016423953159369330679 := by
  apply lucas_primality 1016423953159369330679 (11 : ZMod 1016423953159369330679)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (7187, 1), (13757, 1), (5450819747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (7187, 1), (13757, 1), (5450819747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1016423953159369330679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_7187
      · exact prime_thirtyFourAF_13757
      · exact prime_thirtyFourAF_5450819747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1016423953159369330679) ^ 508211976579684665339 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1016423953159369330679) ^ 44192345789537796986 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1016423953159369330679) ^ 24790828125838276358 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1016423953159369330679) ^ 141425344811377394 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1016423953159369330679) ^ 73884128309905454 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1016423953159369330679) ^ 186471760274 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_107
      · exact prime_thirtyFourAF_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3046823232694638117577 : Nat.Prime 3046823232694638117577 := by
  apply lucas_primality 3046823232694638117577 (7 : ZMod 3046823232694638117577)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (1479133, 1), (435674924099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (1479133, 1), (435674924099, 1)] : List FactorBlock).map factorBlockValue).prod) = 3046823232694638117577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_197
      · exact prime_thirtyFourAF_1479133
      · exact prime_thirtyFourAF_435674924099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3046823232694638117577) ^ 1523411616347319058788 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 1015607744231546039192 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 15466107780175828008 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 2059871041140072 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 6993340824 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_23784406505979643974407 : Nat.Prime 23784406505979643974407 := by
  apply lucas_primality 23784406505979643974407 (5 : ZMod 23784406505979643974407)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (47004755940671233151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (47004755940671233151, 1)] : List FactorBlock).map factorBlockValue).prod) = 23784406505979643974407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_47004755940671233151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23784406505979643974407) ^ 11892203252989821987203 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 2162218773270876724946 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 1034104630694767129322 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 506 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_39888734144558519737813 : Nat.Prime 39888734144558519737813 := by
  apply lucas_primality 39888734144558519737813 (2 : ZMod 39888734144558519737813)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (137, 1), (1327, 1), (426407, 1), (424552907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (137, 1), (1327, 1), (426407, 1), (424552907, 1)] : List FactorBlock).map factorBlockValue).prod) = 39888734144558519737813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_101
      · exact prime_thirtyFourAF_137
      · exact prime_thirtyFourAF_1327
      · exact prime_thirtyFourAF_426407
      · exact prime_thirtyFourAF_424552907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39888734144558519737813) ^ 19944367072279259868906 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 13296244714852839912604 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 394937961827312076612 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 291158643390938100276 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 30059332437497000556 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 93546152254907916 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 93954683825916 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_48277002932255897663783 : Nat.Prime 48277002932255897663783 := by
  apply lucas_primality 48277002932255897663783 (5 : ZMod 48277002932255897663783)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83047, 1), (13251499, 1), (21934177247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83047, 1), (13251499, 1), (21934177247, 1)] : List FactorBlock).map factorBlockValue).prod) = 48277002932255897663783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_83047
      · exact prime_thirtyFourAF_13251499
      · exact prime_thirtyFourAF_21934177247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48277002932255897663783) ^ 24138501466127948831891 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 581321455708886506 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 3643135235663218 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 2200994474906 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_67635063861731679735407 : Nat.Prime 67635063861731679735407 := by
  apply lucas_primality 67635063861731679735407 (5 : ZMod 67635063861731679735407)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2851, 1), (21997, 1), (539238927990449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2851, 1), (21997, 1), (539238927990449, 1)] : List FactorBlock).map factorBlockValue).prod) = 67635063861731679735407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_2851
      · exact prime_thirtyFourAF_21997
      · exact prime_thirtyFourAF_539238927990449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 67635063861731679735407) ^ 33817531930865839867703 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 67635063861731679735407) ^ 23723277398011813306 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 67635063861731679735407) ^ 3074740367401540198 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 67635063861731679735407) ^ 125426894 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_286456968177416405454383 : Nat.Prime 286456968177416405454383 := by
  apply lucas_primality 286456968177416405454383 (5 : ZMod 286456968177416405454383)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (48662543, 1), (15739574530651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (48662543, 1), (15739574530651, 1)] : List FactorBlock).map factorBlockValue).prod) = 286456968177416405454383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_48662543
      · exact prime_thirtyFourAF_15739574530651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 286456968177416405454383) ^ 143228484088708202727191 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 286456968177416405454383) ^ 26041542561583309586762 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 286456968177416405454383) ^ 16850409892789200320846 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 286456968177416405454383) ^ 5886600874463474 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 286456968177416405454383) ^ 18199791082 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_318294341229212022388223 : Nat.Prime 318294341229212022388223 := by
  apply lucas_primality 318294341229212022388223 (5 : ZMod 318294341229212022388223)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (231841, 1), (12640889, 1), (3194347367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (231841, 1), (12640889, 1), (3194347367, 1)] : List FactorBlock).map factorBlockValue).prod) = 318294341229212022388223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_231841
      · exact prime_thirtyFourAF_12640889
      · exact prime_thirtyFourAF_3194347367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 318294341229212022388223) ^ 159147170614606011194111 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 318294341229212022388223) ^ 18723196542894824846366 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 318294341229212022388223) ^ 1372899276785434942 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 318294341229212022388223) ^ 25179743389029998 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 318294341229212022388223) ^ 99642995786066 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_390790232055841933243759 : Nat.Prime 390790232055841933243759 := by
  apply lucas_primality 390790232055841933243759 (3 : ZMod 390790232055841933243759)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1249, 1), (154791467, 1), (336886024471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1249, 1), (154791467, 1), (336886024471, 1)] : List FactorBlock).map factorBlockValue).prod) = 390790232055841933243759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_1249
      · exact prime_thirtyFourAF_154791467
      · exact prime_thirtyFourAF_336886024471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 390790232055841933243759) ^ 195395116027920966621879 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 390790232055841933243759) ^ 130263410685280644414586 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 390790232055841933243759) ^ 312882491637983933742 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 390790232055841933243759) ^ 2524623867385674 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 390790232055841933243759) ^ 1160007253698 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_449330137038854874752809 : Nat.Prime 449330137038854874752809 := by
  apply lucas_primality 449330137038854874752809 (7 : ZMod 449330137038854874752809)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (599, 1), (31255574362747278433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (599, 1), (31255574362747278433, 1)] : List FactorBlock).map factorBlockValue).prod) = 449330137038854874752809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_599
      · exact prime_thirtyFourAF_31255574362747278433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 449330137038854874752809) ^ 224665068519427437376404 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 149776712346284958250936 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 750133784705934682392 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 14376 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1719587357096849636181823 : Nat.Prime 1719587357096849636181823 := by
  apply lucas_primality 1719587357096849636181823 (5 : ZMod 1719587357096849636181823)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6827, 1), (95430239, 1), (146634385643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6827, 1), (95430239, 1), (146634385643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1719587357096849636181823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_6827
      · exact prime_thirtyFourAF_95430239
      · exact prime_thirtyFourAF_146634385643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1719587357096849636181823) ^ 859793678548424818090911 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 573195785698949878727274 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 251880380415533856186 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 18019313114125698 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 11727040349754 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_3985037579012189659500971 : Nat.Prime 3985037579012189659500971 := by
  apply lucas_primality 3985037579012189659500971 (2 : ZMod 3985037579012189659500971)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (24847, 1), (13879277, 1), (8080822741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (24847, 1), (13879277, 1), (8080822741, 1)] : List FactorBlock).map factorBlockValue).prod) = 3985037579012189659500971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_24847
      · exact prime_thirtyFourAF_13879277
      · exact prime_thirtyFourAF_8080822741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3985037579012189659500971) ^ 1992518789506094829750485 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3985037579012189659500971) ^ 797007515802437931900194 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3985037579012189659500971) ^ 362276143546562696318270 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3985037579012189659500971) ^ 306541352231706896884690 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3985037579012189659500971) ^ 160383047410640707510 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3985037579012189659500971) ^ 287121409783246610 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3985037579012189659500971) ^ 493147505735170 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_31453109592719841232696631 : Nat.Prime 31453109592719841232696631 := by
  apply lucas_primality 31453109592719841232696631 (11 : ZMod 31453109592719841232696631)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (449330137038854874752809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (449330137038854874752809, 1)] : List FactorBlock).map factorBlockValue).prod) = 31453109592719841232696631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_449330137038854874752809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 31453109592719841232696631) ^ 15726554796359920616348315 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 6290621918543968246539326 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 4493301370388548747528090 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 70 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_59200403622232631951968033 : Nat.Prime 59200403622232631951968033 := by
  apply lucas_primality 59200403622232631951968033 (5 : ZMod 59200403622232631951968033)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2503, 1), (246372701184547842389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2503, 1), (246372701184547842389, 1)] : List FactorBlock).map factorBlockValue).prod) = 59200403622232631951968033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_2503
      · exact prime_thirtyFourAF_246372701184547842389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59200403622232631951968033) ^ 29600201811116315975984016 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 59200403622232631951968033) ^ 19733467874077543983989344 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 59200403622232631951968033) ^ 23651779313716592869344 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (5 : ZMod 59200403622232631951968033) ^ 240288 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_410174225096897521381492801 : Nat.Prime 410174225096897521381492801 := by
  apply lucas_primality 410174225096897521381492801 (14 : ZMod 410174225096897521381492801)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 410174225096897521381492801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 410174225096897521381492801) ^ 205087112548448760690746400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 136724741698965840460497600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 82034845019379504276298560 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 37288565917899774671044800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 31551863468992117029345600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 24127895593935148316558400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 21588117110363027441131200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 17833661960734674842673600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 14143938796444742116603200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 13231426616028952302628800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 11085789867483716794094400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 10004249392607256619060800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 9538935467369709799569600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 8727111172274415348542400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 7739136322582972101537600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 6952105510116907142059200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 6724167624539303629204800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_490208220237755574333979201 : Nat.Prime 490208220237755574333979201 := by
  apply lucas_primality 490208220237755574333979201 (67 : ZMod 490208220237755574333979201)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 490208220237755574333979201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 490208220237755574333979201) ^ 245104110118877787166989600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 163402740079251858111326400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 98041644047551114866795840 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 70029745748250796333425600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 44564383657977779484907200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 37708324633673505717998400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 28835777661044445549057600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 25800432644092398649156800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 21313400879902416275390400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 16903731732336399114964800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 15813168394766308849483200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 13248870817236637144161600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 11400191168319897077534400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 10429962132718203709233600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 9249211702599161779886400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 8308613902334840242948800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 8036200331766484825147200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_543203703506702122910625601 : Nat.Prime 543203703506702122910625601 := by
  apply lucas_primality 543203703506702122910625601 (71 : ZMod 543203703506702122910625601)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 543203703506702122910625601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 543203703506702122910625601) ^ 271601851753351061455312800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 181067901168900707636875200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 108640740701340424582125120 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 77600529072386017558660800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 49382154864245647537329600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 41784900269746317146971200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 31953159029806007230036800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 28589668605615901205822400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 23617552326378353170027200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 18731162189886280100366400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 17522700113119423319697600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 13248870817236637144161600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 12632644267597723788619200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 11557525606525577083204800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 10249126481258530620955200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 9206842432316985134078400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 8904978746011510211649600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_648339904185418662828811201 : Nat.Prime 648339904185418662828811201 := by
  apply lucas_primality 648339904185418662828811201 (73 : ZMod 648339904185418662828811201)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 648339904185418662828811201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 648339904185418662828811201) ^ 324169952092709331414405600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 216113301395139554276270400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 129667980837083732565762240 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 92619986312202666118401600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 58939991289583514802619200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 49872300321955281756062400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 38137641422671686048753600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 34123152851864140148884800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 28188691486322550557774400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 22356548420186850442372800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 17522700113119423319697600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 15813168394766308849483200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 15077672190358573554158400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 13794466046498269421889600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 12232828380856955902430400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 10988811935346079030996800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 10628523019433092833259200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1546041309980613734437934401 : Nat.Prime 1546041309980613734437934401 := by
  apply lucas_primality 1546041309980613734437934401 (26 : ZMod 1546041309980613734437934401)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546041309980613734437934401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1546041309980613734437934401) ^ 773020654990306867218967200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 515347103326871244812644800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 309208261996122746887586880 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 220863044282944819205419200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 140549209998237612221630400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 90943606469447866731643200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 81370595262137564970417600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 67219187390461466714692800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 53311769309676335670273600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 49872300321955281756062400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 41784900269746317146971200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 37708324633673505717998400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 35954449069316598475300800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 32894495957034334775275200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 29170590754351202536564800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 26204089999671419227761600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 25344939507878913679310400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_1674878085812331545641095601 : Nat.Prime 1674878085812331545641095601 := by
  apply lucas_primality 1674878085812331545641095601 (107 : ZMod 1674878085812331545641095601)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674878085812331545641095601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1674878085812331545641095601) ^ 837439042906165772820547800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 558292695270777181880365200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 334975617162466309128219120 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 239268297973190220805870800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 152261644164757413240099600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 128836775831717811203161200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 98522240341901855625946800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 88151478200649028717952400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 72820786339666588940917200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 57754416752149363642796400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 54028325348784888569067600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 45266975292225176909218800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 40850685019812964527831600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 38950653158426315014909200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 35635703953453862673214800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 31601473317213802747945200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 28387764166310704163408400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 27457017800202156485919600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_10049268514873989273846573601 : Nat.Prime 10049268514873989273846573601 := by
  apply lucas_primality 10049268514873989273846573601 (103 : ZMod 10049268514873989273846573601)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 10049268514873989273846573601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_5
      · exact prime_thirtyFourAF_7
      · exact prime_thirtyFourAF_11
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_17
      · exact prime_thirtyFourAF_19
      · exact prime_thirtyFourAF_23
      · exact prime_thirtyFourAF_29
      · exact prime_thirtyFourAF_31
      · exact prime_thirtyFourAF_37
      · exact prime_thirtyFourAF_41
      · exact prime_thirtyFourAF_43
      · exact prime_thirtyFourAF_47
      · exact prime_thirtyFourAF_53
      · exact prime_thirtyFourAF_59
      · exact prime_thirtyFourAF_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 10049268514873989273846573601) ^ 5024634257436994636923286800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 3349756171624663091282191200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 2009853702974797854769314720 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 1435609787839141324835224800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 913569864988544479440597600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 773020654990306867218967200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 591133442051411133755680800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 528908869203894172307714400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 436924718037999533645503200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 346526500512896181856778400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 324169952092709331414405600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 271601851753351061455312800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 245104110118877787166989600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 233703918950557890089455200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 213814223720723176039288800 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 189608839903282816487671200 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 170326584997864224980450400 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 164742106801212938915517600 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_40197074059495957095386294473 : Nat.Prime 40197074059495957095386294473 := by
  apply lucas_primality 40197074059495957095386294473 (10 : ZMod 40197074059495957095386294473)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1373, 1), (1993, 1), (304357847, 1), (670346901547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1373, 1), (1993, 1), (304357847, 1), (670346901547, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_1373
      · exact prime_thirtyFourAF_1993
      · exact prime_thirtyFourAF_304357847
      · exact prime_thirtyFourAF_670346901547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 40197074059495957095386294473) ^ 20098537029747978547693147236 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 40197074059495957095386294473) ^ 13399024686498652365128764824 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 40197074059495957095386294473) ^ 29276820145299313252284264 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 40197074059495957095386294473) ^ 20169128981182115953530504 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 40197074059495957095386294473) ^ 132071751905565152376 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (10 : ZMod 40197074059495957095386294473) ^ 59964585450802776 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem prime_thirtyFourAF_40197074059495957095386294479 : Nat.Prime 40197074059495957095386294479 := by
  apply lucas_primality 40197074059495957095386294479 (3 : ZMod 40197074059495957095386294479)
  · rw [← thirtyFourAFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (763157, 1), (675283202967241661693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (763157, 1), (675283202967241661693, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyFourAF_2
      · exact prime_thirtyFourAF_3
      · exact prime_thirtyFourAF_13
      · exact prime_thirtyFourAF_763157
      · exact prime_thirtyFourAF_675283202967241661693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40197074059495957095386294479) ^ 20098537029747978547693147239 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495957095386294479) ^ 13399024686498652365128764826 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495957095386294479) ^ 3092082619961227468875868806 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495957095386294479) ^ 52672089831444849612054 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40197074059495957095386294479) ^ 59526246 ≠ 1
      rw [← thirtyFourAFFastPow_eq_pow]
      decide

private theorem phi_thirtyFourAF_40197074059495957095386294400 : Nat.totient 40197074059495957095386294400 = 5289426527618261739110400000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_7, prime_thirtyFourAF_11, prime_thirtyFourAF_13, prime_thirtyFourAF_17, prime_thirtyFourAF_19, prime_thirtyFourAF_23, prime_thirtyFourAF_29, prime_thirtyFourAF_31, prime_thirtyFourAF_37, prime_thirtyFourAF_41, prime_thirtyFourAF_43, prime_thirtyFourAF_47, prime_thirtyFourAF_53, prime_thirtyFourAF_59, prime_thirtyFourAF_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294401 : Nat.totient 40197074059495957095386294401 = 40196759137258274216724598848 := by
  rw [← show ((([(129119, 1), (13072109, 1), (129192733, 1), (184340407, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_129119, prime_thirtyFourAF_13072109, prime_thirtyFourAF_129192733, prime_thirtyFourAF_184340407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294402 : Nat.totient 40197074059495957095386294402 = 20089694715434961712395596160 := by
  rw [← show ((([(2, 1), (2273, 1), (1052072531, 1), (8404644125874427, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_2273, prime_thirtyFourAF_1052072531, prime_thirtyFourAF_8404644125874427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294403 : Nat.totient 40197074059495957095386294403 = 26797508558431290113833512960 := by
  rw [← show ((([(3, 1), (57641, 1), (353057, 1), (658410660431626873, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_57641, prime_thirtyFourAF_353057, prime_thirtyFourAF_658410660431626873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294404 : Nat.totient 40197074059495957095386294404 = 20098537029747978547693147200 := by
  rw [← show ((([(2, 2), (10049268514873989273846573601, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_10049268514873989273846573601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294405 : Nat.totient 40197074059495957095386294405 = 32157658576969972656958456848 := by
  rw [← show ((([(5, 1), (47951647, 1), (167656698254789693023, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_47951647, prime_thirtyFourAF_167656698254789693023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294406 : Nat.totient 40197074059495957095386294406 = 13394834325010510836904177920 := by
  rw [← show ((([(2, 1), (3, 1), (3863, 1), (19891, 1), (299027, 1), (3960137, 1), (73627703, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_3863, prime_thirtyFourAF_19891, prime_thirtyFourAF_299027, prime_thirtyFourAF_3960137, prime_thirtyFourAF_73627703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294407 : Nat.totient 40197074059495957095386294407 = 34099432486405996004333586432 := by
  rw [← show ((([(7, 1), (97, 1), (59200403622232631951968033, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_7, prime_thirtyFourAF_97, prime_thirtyFourAF_59200403622232631951968033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294408 : Nat.totient 40197074059495957095386294408 = 20098537029339085283335598016 := by
  rw [← show ((([(2, 3), (49153528429, 1), (102223266935858869, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_49153528429, prime_thirtyFourAF_102223266935858869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294409 : Nat.totient 40197074059495957095386294409 = 26796922492479250588706476800 := by
  rw [← show ((([(3, 2), (33479, 1), (82139, 1), (139585741, 1), (11635605481, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_33479, prime_thirtyFourAF_82139, prime_thirtyFourAF_139585741, prime_thirtyFourAF_11635605481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294410 : Nat.totient 40197074059495957095386294410 = 15875299685995237821163364352 := by
  rw [← show ((([(2, 1), (5, 1), (79, 1), (52142977, 1), (111306893, 1), (8766968939, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_5, prime_thirtyFourAF_79, prime_thirtyFourAF_52142977, prime_thirtyFourAF_111306893, prime_thirtyFourAF_8766968939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294411 : Nat.totient 40197074059495957095386294411 = 36483214716499672835011620000 := by
  rw [← show ((([(11, 1), (659, 1), (8839, 1), (627354775635530615501, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_11, prime_thirtyFourAF_659, prime_thirtyFourAF_8839, prime_thirtyFourAF_627354775635530615501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294412 : Nat.totient 40197074059495957095386294412 = 13368491542901207542644417408 := by
  rw [← show ((([(2, 2), (3, 1), (439, 1), (1167833, 1), (6533831533403812223, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_439, prime_thirtyFourAF_1167833, prime_thirtyFourAF_6533831533403812223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294413 : Nat.totient 40197074059495957095386294413 = 37027430160517044471588543360 := by
  rw [← show ((([(13, 1), (521, 1), (5839, 1), (1016423953159369330679, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_13, prime_thirtyFourAF_521, prime_thirtyFourAF_5839, prime_thirtyFourAF_1016423953159369330679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294414 : Nat.totient 40197074059495957095386294414 = 17226778612256449479044952192 := by
  rw [← show ((([(2, 1), (7, 1), (54833, 1), (76679, 1), (682885605572149543, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_7, prime_thirtyFourAF_54833, prime_thirtyFourAF_76679, prime_thirtyFourAF_682885605572149543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294415 : Nat.totient 40197074059495957095386294415 = 21296462756779527897800160000 := by
  rw [← show ((([(3, 1), (5, 1), (151, 1), (66323641, 1), (267582603990315871, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_151, prime_thirtyFourAF_66323641, prime_thirtyFourAF_267582603990315871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294416 : Nat.totient 40197074059495957095386294416 = 20093832662412838958298316800 := by
  rw [← show ((([(2, 4), (4801, 1), (40163, 1), (1133689, 1), (11492716013243, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_4801, prime_thirtyFourAF_40163, prime_thirtyFourAF_1133689, prime_thirtyFourAF_11492716013243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294417 : Nat.totient 40197074059495957095386294417 = 37832360301755497936121720832 := by
  rw [← show ((([(17, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_17, prime_thirtyFourAF_210193, prime_thirtyFourAF_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294418 : Nat.totient 40197074059495957095386294418 = 13210306028942333317732584600 := by
  rw [← show ((([(2, 1), (3, 2), (71, 1), (31453109592719841232696631, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_71, prime_thirtyFourAF_31453109592719841232696631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294419 : Nat.totient 40197074059495957095386294419 = 37501548286444305863482688544 := by
  rw [← show ((([(19, 1), (67, 1), (3259, 1), (3193766699, 1), (3033740920883, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_19, prime_thirtyFourAF_67, prime_thirtyFourAF_3259, prime_thirtyFourAF_3193766699, prime_thirtyFourAF_3033740920883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294420 : Nat.totient 40197074059495957095386294420 = 16078639348546335001002046496 := by
  rw [← show ((([(2, 2), (5, 1), (84503, 1), (23784406505979643974407, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_5, prime_thirtyFourAF_84503, prime_thirtyFourAF_23784406505979643974407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294421 : Nat.totient 40197074059495957095386294421 = 22934227073548042468951479360 := by
  rw [← show ((([(3, 1), (7, 1), (757, 1), (4423, 1), (571692280977967567291, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_7, prime_thirtyFourAF_757, prime_thirtyFourAF_4423, prime_thirtyFourAF_571692280977967567291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294422 : Nat.totient 40197074059495957095386294422 = 18270914529741567029834935720 := by
  rw [← show ((([(2, 1), (11, 1), (37847, 1), (48277002932255897663783, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_11, prime_thirtyFourAF_37847, prime_thirtyFourAF_48277002932255897663783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294423 : Nat.totient 40197074059495957095386294423 = 38449375187316554294776412800 := by
  rw [← show ((([(23, 1), (1404606769961, 1), (1244262030860441, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_23, prime_thirtyFourAF_1404606769961, prime_thirtyFourAF_1244262030860441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294424 : Nat.totient 40197074059495957095386294424 = 13399024686498652365128764800 := by
  rw [← show ((([(2, 3), (3, 1), (1674878085812331545641095601, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_1674878085812331545641095601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294425 : Nat.totient 40197074059495957095386294425 = 31523268950707057005290618880 := by
  rw [← show ((([(5, 2), (113, 1), (149, 1), (233, 1), (2990957, 1), (3794083, 1), (36117427, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_113, prime_thirtyFourAF_149, prime_thirtyFourAF_233, prime_thirtyFourAF_2990957, prime_thirtyFourAF_3794083, prime_thirtyFourAF_36117427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294426 : Nat.totient 40197074059495957095386294426 = 18552495719767364813255212800 := by
  rw [← show ((([(2, 1), (13, 1), (1546041309980613734437934401, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_13, prime_thirtyFourAF_1546041309980613734437934401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294427 : Nat.totient 40197074059495957095386294427 = 26777846859605919846625683456 := by
  rw [← show ((([(3, 3), (1459, 1), (14593, 1), (69924730862683817723, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_1459, prime_thirtyFourAF_14593, prime_thirtyFourAF_69924730862683817723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294428 : Nat.totient 40197074059495957095386294428 = 17225380226836514425896612864 := by
  rw [← show ((([(2, 2), (7, 1), (8893, 1), (344755493, 1), (468249070338449, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_7, prime_thirtyFourAF_8893, prime_thirtyFourAF_344755493, prime_thirtyFourAF_468249070338449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294429 : Nat.totient 40197074059495957095386294429 = 38810968022258724659843989296 := by
  rw [← show ((([(29, 1), (1103034067, 1), (1256630274186794203, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_29, prime_thirtyFourAF_1103034067, prime_thirtyFourAF_1256630274186794203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294430 : Nat.totient 40197074059495957095386294430 = 10695260366395870073208035328 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (743, 1), (1123, 1), (88685873, 1), (18107153021773, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_743, prime_thirtyFourAF_1123, prime_thirtyFourAF_88685873, prime_thirtyFourAF_18107153021773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294431 : Nat.totient 40197074059495957095386294431 = 38900394248398447021793136120 := by
  rw [← show ((([(31, 1), (14266618679, 1), (90889077331232519, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_31, prime_thirtyFourAF_14266618679, prime_thirtyFourAF_90889077331232519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294432 : Nat.totient 40197074059495957095386294432 = 20087533331840496319801344000 := by
  rw [← show ((([(2, 5), (2693, 1), (5701, 1), (1231261, 1), (66451830061937, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_2693, prime_thirtyFourAF_5701, prime_thirtyFourAF_1231261, prime_thirtyFourAF_66451830061937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294433 : Nat.totient 40197074059495957095386294433 = 24227267063564546823656707200 := by
  rw [← show ((([(3, 1), (11, 2), (181, 2), (326289343, 1), (10359237208517, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_11, prime_thirtyFourAF_181, prime_thirtyFourAF_326289343, prime_thirtyFourAF_10359237208517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294434 : Nat.totient 40197074059495957095386294434 = 18728877245652730232015619072 := by
  rw [← show ((([(2, 1), (17, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_17, prime_thirtyFourAF_103, prime_thirtyFourAF_5009, prime_thirtyFourAF_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294435 : Nat.totient 40197074059495957095386294435 = 27172928355692880805700198400 := by
  rw [← show ((([(5, 1), (7, 1), (73, 1), (2393, 1), (14851, 1), (6765023, 1), (65438880853, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_7, prime_thirtyFourAF_73, prime_thirtyFourAF_2393, prime_thirtyFourAF_14851, prime_thirtyFourAF_6765023, prime_thirtyFourAF_65438880853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294436 : Nat.totient 40197074059495957095386294436 = 13363164909222340469953867776 := by
  rw [← show ((([(2, 2), (3, 2), (397, 1), (6337, 1), (443831096543292924709, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_397, prime_thirtyFourAF_6337, prime_thirtyFourAF_443831096543292924709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294437 : Nat.totient 40197074059495957095386294437 = 38074436256634378569131328000 := by
  rw [← show ((([(37, 1), (89, 1), (101, 1), (179, 1), (675193583599945710071, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_37, prime_thirtyFourAF_89, prime_thirtyFourAF_101, prime_thirtyFourAF_179, prime_thirtyFourAF_675193583599945710071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294438 : Nat.totient 40197074059495957095386294438 = 18859385520008252838548213760 := by
  rw [← show ((([(2, 1), (19, 1), (109, 1), (2857, 1), (439441, 1), (9978323, 1), (774668639, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_19, prime_thirtyFourAF_109, prime_thirtyFourAF_2857, prime_thirtyFourAF_439441, prime_thirtyFourAF_9978323, prime_thirtyFourAF_774668639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294439 : Nat.totient 40197074059495957095386294439 = 24736546532937176386784099232 := by
  rw [← show ((([(3, 1), (13, 2), (216179, 1), (366752412318474857063, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_13, prime_thirtyFourAF_216179, prime_thirtyFourAF_366752412318474857063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294440 : Nat.totient 40197074059495957095386294440 = 16054573684073352997834137600 := by
  rw [← show ((([(2, 3), (5, 1), (887, 1), (3637, 1), (11317, 1), (54601, 1), (504121961207, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_5, prime_thirtyFourAF_887, prime_thirtyFourAF_3637, prime_thirtyFourAF_11317, prime_thirtyFourAF_54601, prime_thirtyFourAF_504121961207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294441 : Nat.totient 40197074059495957095386294441 = 39212295656545240008442624000 := by
  rw [← show ((([(41, 1), (10037, 1), (86243, 1), (833538191, 1), (1358805521, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_41, prime_thirtyFourAF_10037, prime_thirtyFourAF_86243, prime_thirtyFourAF_833538191, prime_thirtyFourAF_1358805521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294442 : Nat.totient 40197074059495957095386294442 = 11484878296664508317990826048 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1898759389, 1), (504051854825488309, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_7, prime_thirtyFourAF_1898759389, prime_thirtyFourAF_504051854825488309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294443 : Nat.totient 40197074059495957095386294443 = 39169282054145291533715489280 := by
  rw [← show ((([(43, 1), (433, 1), (17021, 1), (126839061027076803557, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_43, prime_thirtyFourAF_433, prime_thirtyFourAF_17021, prime_thirtyFourAF_126839061027076803557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294444 : Nat.totient 40197074059495957095386294444 = 18270813902962957596702321600 := by
  rw [← show ((([(2, 2), (11, 1), (31319, 1), (111179436971, 1), (262367120149, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_11, prime_thirtyFourAF_31319, prime_thirtyFourAF_111179436971, prime_thirtyFourAF_262367120149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294445 : Nat.totient 40197074059495957095386294445 = 21437073071404228764085722624 := by
  rw [← show ((([(3, 2), (5, 1), (15749, 1), (6549019, 1), (11475509, 1), (754711099, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_15749, prime_thirtyFourAF_6549019, prime_thirtyFourAF_11475509, prime_thirtyFourAF_754711099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294446 : Nat.totient 40197074059495957095386294446 = 19224628848785001450671765760 := by
  rw [← show ((([(2, 1), (23, 1), (327263, 1), (21764550497, 1), (122684585791, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_23, prime_thirtyFourAF_327263, prime_thirtyFourAF_21764550497, prime_thirtyFourAF_122684585791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294447 : Nat.totient 40197074059495957095386294447 = 39327175624916520638199157432 := by
  rw [← show ((([(47, 1), (2687, 1), (318294341229212022388223, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_47, prime_thirtyFourAF_2687, prime_thirtyFourAF_318294341229212022388223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294448 : Nat.totient 40197074059495957095386294448 = 13371511288785102770949847872 := by
  rw [← show ((([(2, 4), (3, 1), (487, 1), (1719587357096849636181823, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_487, prime_thirtyFourAF_1719587357096849636181823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294449 : Nat.totient 40197074059495957095386294449 = 34454622475284947715357696384 := by
  rw [← show ((([(7, 2), (2771257, 1), (296020343906680269193, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_7, prime_thirtyFourAF_2771257, prime_thirtyFourAF_296020343906680269193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294450 : Nat.totient 40197074059495957095386294450 = 15949740735921967321248276480 := by
  rw [← show ((([(2, 1), (5, 2), (197, 1), (337, 1), (16046729, 1), (754643424782869, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_5, prime_thirtyFourAF_197, prime_thirtyFourAF_337, prime_thirtyFourAF_16046729, prime_thirtyFourAF_754643424782869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294451 : Nat.totient 40197074059495957095386294451 = 25144795668174382594308096000 := by
  rw [← show ((([(3, 1), (17, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_17, prime_thirtyFourAF_421, prime_thirtyFourAF_1483, prime_thirtyFourAF_2072201, prime_thirtyFourAF_2567179, prime_thirtyFourAF_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294452 : Nat.totient 40197074059495957095386294452 = 18552491099672826914414254080 := by
  rw [← show ((([(2, 2), (13, 1), (4930417, 1), (21642461, 1), (7244372988773, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_13, prime_thirtyFourAF_4930417, prime_thirtyFourAF_21642461, prime_thirtyFourAF_7244372988773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294453 : Nat.totient 40197074059495957095386294453 = 39389888820978827300781655680 := by
  rw [← show ((([(53, 1), (809, 1), (2389974799, 1), (392262443383511, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_53, prime_thirtyFourAF_809, prime_thirtyFourAF_2389974799, prime_thirtyFourAF_392262443383511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294454 : Nat.totient 40197074059495957095386294454 = 13399012235293974285535623168 := by
  rw [← show ((([(2, 1), (3, 6), (1076753, 1), (2179651489, 1), (11747183939, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_1076753, prime_thirtyFourAF_2179651489, prime_thirtyFourAF_11747183939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294455 : Nat.totient 40197074059495957095386294455 = 29198535430103655557990400000 := by
  rw [← show ((([(5, 1), (11, 1), (821, 1), (316801, 1), (2809972382947583261, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_11, prime_thirtyFourAF_821, prime_thirtyFourAF_316801, prime_thirtyFourAF_2809972382947583261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294456 : Nat.totient 40197074059495957095386294456 = 17227317251811354607377360000 := by
  rw [← show ((([(2, 3), (7, 1), (122594851, 1), (282861461, 1), (20699526191, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_7, prime_thirtyFourAF_122594851, prime_thirtyFourAF_282861461, prime_thirtyFourAF_20699526191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294457 : Nat.totient 40197074059495957095386294457 = 25387331715068018561232344640 := by
  rw [← show ((([(3, 1), (19, 1), (127343, 1), (449671, 1), (664879, 1), (18522816023, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_19, prime_thirtyFourAF_127343, prime_thirtyFourAF_449671, prime_thirtyFourAF_664879, prime_thirtyFourAF_18522816023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294458 : Nat.totient 40197074059495957095386294458 = 19288195945570901143322465280 := by
  rw [← show ((([(2, 1), (29, 1), (167, 1), (19421, 1), (223283, 1), (2432869, 1), (393372509, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_29, prime_thirtyFourAF_167, prime_thirtyFourAF_19421, prime_thirtyFourAF_223283, prime_thirtyFourAF_2432869, prime_thirtyFourAF_393372509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294459 : Nat.totient 40197074059495957095386294459 = 39515758143841881088727436000 := by
  rw [← show ((([(59, 1), (5261647, 1), (19131283, 1), (6768253648501, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_59, prime_thirtyFourAF_5261647, prime_thirtyFourAF_19131283, prime_thirtyFourAF_6768253648501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294460 : Nat.totient 40197074059495957095386294460 = 10672398600450814222599436032 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (229, 1), (865643, 1), (3379627908495294503, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_229, prime_thirtyFourAF_865643, prime_thirtyFourAF_3379627908495294503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294461 : Nat.totient 40197074059495957095386294461 = 39534047528459401438939515120 := by
  rw [← show ((([(61, 1), (9743, 1), (67635063861731679735407, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_61, prime_thirtyFourAF_9743, prime_thirtyFourAF_67635063861731679735407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294462 : Nat.totient 40197074059495957095386294462 = 19450197125562559884864336000 := by
  rw [← show ((([(2, 1), (31, 1), (648339904185418662828811201, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_31, prime_thirtyFourAF_648339904185418662828811201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294463 : Nat.totient 40197074059495957095386294463 = 22966991836877917570003066368 := by
  rw [← show ((([(3, 2), (7, 1), (8929, 1), (119447, 1), (598240516789697927, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_7, prime_thirtyFourAF_8929, prime_thirtyFourAF_119447, prime_thirtyFourAF_598240516789697927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294464 : Nat.totient 40197074059495957095386294464 = 20098534277997233877998377728 := by
  rw [← show ((([(2, 6), (7303909, 1), (85992210770920657639, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_7303909, prime_thirtyFourAF_85992210770920657639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294465 : Nat.totient 40197074059495957095386294465 = 29683891438068245431770270720 := by
  rw [← show ((([(5, 1), (13, 1), (291923, 1), (1015858667, 1), (2085352522321, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_13, prime_thirtyFourAF_291923, prime_thirtyFourAF_1015858667, prime_thirtyFourAF_2085352522321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294466 : Nat.totient 40197074059495957095386294466 = 12180927946332795642063936080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (3395999, 1), (179342389870853805599, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_11, prime_thirtyFourAF_3395999, prime_thirtyFourAF_179342389870853805599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294467 : Nat.totient 40197074059495957095386294467 = 40129678516117955668007802048 := by
  rw [← show ((([(647, 1), (8087, 1), (131899, 1), (58245344094475897, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_647, prime_thirtyFourAF_8087, prime_thirtyFourAF_131899, prime_thirtyFourAF_58245344094475897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294468 : Nat.totient 40197074059495957095386294468 = 18916270130173191852230595200 := by
  rw [← show ((([(2, 2), (17, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_17, prime_thirtyFourAF_1222615931, prime_thirtyFourAF_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294469 : Nat.totient 40197074059495957095386294469 = 25632916791522368039128459328 := by
  rw [← show ((([(3, 1), (23, 1), (636949592813, 1), (914619143007077, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_23, prime_thirtyFourAF_636949592813, prime_thirtyFourAF_914619143007077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294470 : Nat.totient 40197074059495957095386294470 = 13781780839498172047098812928 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (188473, 1), (3046823232694638117577, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_5, prime_thirtyFourAF_7, prime_thirtyFourAF_188473, prime_thirtyFourAF_3046823232694638117577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294471 : Nat.totient 40197074059495957095386294471 = 39712771962365483184631278840 := by
  rw [← show ((([(83, 1), (1418482166971, 1), (341422760454247, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_83, prime_thirtyFourAF_1418482166971, prime_thirtyFourAF_341422760454247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294472 : Nat.totient 40197074059495957095386294472 = 13382547556074900938677103616 := by
  rw [← show ((([(2, 3), (3, 2), (1373, 1), (1993, 1), (304357847, 1), (670346901547, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_1373, prime_thirtyFourAF_1993, prime_thirtyFourAF_304357847, prime_thirtyFourAF_670346901547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294473 : Nat.totient 40197074059495957095386294473 = 40197074059495957095386294472 := by
  rw [← show ((([(40197074059495957095386294473, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_40197074059495957095386294473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294474 : Nat.totient 40197074059495957095386294474 = 19555333326241276424782521600 := by
  rw [← show ((([(2, 1), (37, 1), (543203703506702122910625601, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_37, prime_thirtyFourAF_543203703506702122910625601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294475 : Nat.totient 40197074059495957095386294475 = 21426981219670747127987773600 := by
  rw [← show ((([(3, 1), (5, 2), (1871, 1), (286456968177416405454383, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_1871, prime_thirtyFourAF_286456968177416405454383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294476 : Nat.totient 40197074059495957095386294476 = 19040707028882976910215986880 := by
  rw [← show ((([(2, 2), (19, 1), (1553471, 1), (3544788469, 1), (96047789699, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_19, prime_thirtyFourAF_1553471, prime_thirtyFourAF_3544788469, prime_thirtyFourAF_96047789699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294477 : Nat.totient 40197074059495957095386294477 = 31083293116295079344107566000 := by
  rw [← show ((([(7, 1), (11, 1), (131, 1), (3985037579012189659500971, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_7, prime_thirtyFourAF_11, prime_thirtyFourAF_131, prime_thirtyFourAF_3985037579012189659500971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294478 : Nat.totient 40197074059495957095386294478 = 12368314273048038661685278848 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (763157, 1), (675283202967241661693, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_13, prime_thirtyFourAF_763157, prime_thirtyFourAF_675283202967241661693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294479 : Nat.totient 40197074059495957095386294479 = 40197074059495957095386294478 := by
  rw [← show ((([(40197074059495957095386294479, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_40197074059495957095386294479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294480 : Nat.totient 40197074059495957095386294480 = 16078829308081563976303030400 := by
  rw [← show ((([(2, 4), (5, 1), (50928011, 1), (9866150589381930971, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_5, prime_thirtyFourAF_50928011, prime_thirtyFourAF_9866150589381930971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294481 : Nat.totient 40197074059495957095386294481 = 26624847808635436305728640000 := by
  rw [← show ((([(3, 3), (191, 1), (811, 1), (1062361, 1), (11431993, 1), (791375111, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_191, prime_thirtyFourAF_811, prime_thirtyFourAF_1062361, prime_thirtyFourAF_11431993, prime_thirtyFourAF_791375111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294482 : Nat.totient 40197074059495957095386294482 = 19608328809510222973359168000 := by
  rw [← show ((([(2, 1), (41, 1), (490208220237755574333979201, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_41, prime_thirtyFourAF_490208220237755574333979201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294483 : Nat.totient 40197074059495957095386294483 = 40196952781109389045472852160 := by
  rw [← show ((([(331447, 1), (47913011609, 1), (2531202436621, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_331447, prime_thirtyFourAF_47913011609, prime_thirtyFourAF_2531202436621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294484 : Nat.totient 40197074059495957095386294484 = 11484877938317354248441360128 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (32896043, 1), (783928043, 1), (18556467049, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_7, prime_thirtyFourAF_32896043, prime_thirtyFourAF_783928043, prime_thirtyFourAF_18556467049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294485 : Nat.totient 40197074059495957095386294485 = 30132405878005593894360609792 := by
  rw [← show ((([(5, 1), (17, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_17, prime_thirtyFourAF_239, prime_thirtyFourAF_4327, prime_thirtyFourAF_1214459, prime_thirtyFourAF_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294486 : Nat.totient 40197074059495957095386294486 = 19337589101082039294100809600 := by
  rw [← show ((([(2, 1), (43, 1), (67, 1), (36923, 1), (1340981, 1), (140896947156781, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_43, prime_thirtyFourAF_67, prime_thirtyFourAF_36923, prime_thirtyFourAF_1340981, prime_thirtyFourAF_140896947156781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294487 : Nat.totient 40197074059495957095386294487 = 25721755277337400329277092864 := by
  rw [← show ((([(3, 1), (29, 1), (199, 1), (1163, 1), (518233, 1), (1431307, 1), (2691438983, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_29, prime_thirtyFourAF_199, prime_thirtyFourAF_1163, prime_thirtyFourAF_518233, prime_thirtyFourAF_1431307, prime_thirtyFourAF_2691438983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294488 : Nat.totient 40197074059495957095386294488 = 18271397296709035231027972480 := by
  rw [← show ((([(2, 3), (11, 1), (5967429077, 1), (76546352977170413, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_11, prime_thirtyFourAF_5967429077, prime_thirtyFourAF_76546352977170413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294489 : Nat.totient 40197074059495957095386294489 = 39105645375854756028754569600 := by
  rw [← show ((([(71, 1), (79, 1), (1657, 1), (39135331, 1), (110514046803763, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_71, prime_thirtyFourAF_79, prime_thirtyFourAF_1657, prime_thirtyFourAF_39135331, prime_thirtyFourAF_110514046803763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294490 : Nat.totient 40197074059495957095386294490 = 10718262419579452487629035648 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (11197, 1), (39888734144558519737813, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_5, prime_thirtyFourAF_11197, prime_thirtyFourAF_39888734144558519737813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294491 : Nat.totient 40197074059495957095386294491 = 31659800536101932547327774720 := by
  rw [← show ((([(7, 1), (13, 1), (271, 1), (1367, 1), (8039, 1), (176901793, 1), (838457359, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_7, prime_thirtyFourAF_13, prime_thirtyFourAF_271, prime_thirtyFourAF_1367, prime_thirtyFourAF_8039, prime_thirtyFourAF_176901793, prime_thirtyFourAF_838457359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294492 : Nat.totient 40197074059495957095386294492 = 19224687587157902419360300400 := by
  rw [← show ((([(2, 2), (23, 1), (2951252771, 1), (148047202981516331, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_23, prime_thirtyFourAF_2951252771, prime_thirtyFourAF_148047202981516331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294493 : Nat.totient 40197074059495957095386294493 = 25729394622762630351465305280 := by
  rw [← show ((([(3, 1), (31, 1), (127, 1), (1433190624797, 1), (2374672997579, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_31, prime_thirtyFourAF_127, prime_thirtyFourAF_1433190624797, prime_thirtyFourAF_2374672997579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294494 : Nat.totient 40197074059495957095386294494 = 19567772141038379424239454720 := by
  rw [← show ((([(2, 1), (47, 1), (193, 1), (16111, 1), (137526623891778748687, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_47, prime_thirtyFourAF_193, prime_thirtyFourAF_16111, prime_thirtyFourAF_137526623891778748687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294495 : Nat.totient 40197074059495957095386294495 = 30297558003039459112798702080 := by
  rw [← show ((([(5, 1), (19, 1), (227, 1), (1583, 1), (2131, 1), (58035469, 1), (9521099779, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_5, prime_thirtyFourAF_19, prime_thirtyFourAF_227, prime_thirtyFourAF_1583, prime_thirtyFourAF_2131, prime_thirtyFourAF_58035469, prime_thirtyFourAF_9521099779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294496 : Nat.totient 40197074059495957095386294496 = 13273800154884353450547058176 := by
  rw [← show ((([(2, 5), (3, 1), (107, 1), (7237965619, 1), (540658350927197, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_3, prime_thirtyFourAF_107, prime_thirtyFourAF_7237965619, prime_thirtyFourAF_540658350927197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294497 : Nat.totient 40197074059495957095386294497 = 40067460199338157817802040320 := by
  rw [← show ((([(311, 1), (133657, 1), (635617, 1), (1521412008583583, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_311, prime_thirtyFourAF_133657, prime_thirtyFourAF_635617, prime_thirtyFourAF_1521412008583583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294498 : Nat.totient 40197074059495957095386294498 = 17227317454069695898022697600 := by
  rw [← show ((([(2, 1), (7, 2), (410174225096897521381492801, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_2, prime_thirtyFourAF_7, prime_thirtyFourAF_410174225096897521381492801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFourAF_40197074059495957095386294499 : Nat.totient 40197074059495957095386294499 = 24338415652437835602421248240 := by
  rw [← show ((([(3, 2), (11, 1), (1039, 1), (390790232055841933243759, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495957095386294499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFourAF_3, prime_thirtyFourAF_11, prime_thirtyFourAF_1039, prime_thirtyFourAF_390790232055841933243759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyFourAF : certifiedKill 1 40197074059495957095386294399 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyFourAF_40197074059495957095386294400, phi_thirtyFourAF_40197074059495957095386294401, phi_thirtyFourAF_40197074059495957095386294402,
    phi_thirtyFourAF_40197074059495957095386294403, phi_thirtyFourAF_40197074059495957095386294404, phi_thirtyFourAF_40197074059495957095386294405,
    phi_thirtyFourAF_40197074059495957095386294406, phi_thirtyFourAF_40197074059495957095386294407, phi_thirtyFourAF_40197074059495957095386294408,
    phi_thirtyFourAF_40197074059495957095386294409, phi_thirtyFourAF_40197074059495957095386294410, phi_thirtyFourAF_40197074059495957095386294411,
    phi_thirtyFourAF_40197074059495957095386294412, phi_thirtyFourAF_40197074059495957095386294413, phi_thirtyFourAF_40197074059495957095386294414,
    phi_thirtyFourAF_40197074059495957095386294415, phi_thirtyFourAF_40197074059495957095386294416, phi_thirtyFourAF_40197074059495957095386294417,
    phi_thirtyFourAF_40197074059495957095386294418, phi_thirtyFourAF_40197074059495957095386294419, phi_thirtyFourAF_40197074059495957095386294420,
    phi_thirtyFourAF_40197074059495957095386294421, phi_thirtyFourAF_40197074059495957095386294422, phi_thirtyFourAF_40197074059495957095386294423,
    phi_thirtyFourAF_40197074059495957095386294424, phi_thirtyFourAF_40197074059495957095386294425, phi_thirtyFourAF_40197074059495957095386294426,
    phi_thirtyFourAF_40197074059495957095386294427, phi_thirtyFourAF_40197074059495957095386294428, phi_thirtyFourAF_40197074059495957095386294429,
    phi_thirtyFourAF_40197074059495957095386294430, phi_thirtyFourAF_40197074059495957095386294431, phi_thirtyFourAF_40197074059495957095386294432,
    phi_thirtyFourAF_40197074059495957095386294433, phi_thirtyFourAF_40197074059495957095386294434, phi_thirtyFourAF_40197074059495957095386294435,
    phi_thirtyFourAF_40197074059495957095386294436, phi_thirtyFourAF_40197074059495957095386294437, phi_thirtyFourAF_40197074059495957095386294438,
    phi_thirtyFourAF_40197074059495957095386294439, phi_thirtyFourAF_40197074059495957095386294440, phi_thirtyFourAF_40197074059495957095386294441,
    phi_thirtyFourAF_40197074059495957095386294442, phi_thirtyFourAF_40197074059495957095386294443, phi_thirtyFourAF_40197074059495957095386294444,
    phi_thirtyFourAF_40197074059495957095386294445, phi_thirtyFourAF_40197074059495957095386294446, phi_thirtyFourAF_40197074059495957095386294447,
    phi_thirtyFourAF_40197074059495957095386294448, phi_thirtyFourAF_40197074059495957095386294449, phi_thirtyFourAF_40197074059495957095386294450,
    phi_thirtyFourAF_40197074059495957095386294451, phi_thirtyFourAF_40197074059495957095386294452, phi_thirtyFourAF_40197074059495957095386294453,
    phi_thirtyFourAF_40197074059495957095386294454, phi_thirtyFourAF_40197074059495957095386294455, phi_thirtyFourAF_40197074059495957095386294456,
    phi_thirtyFourAF_40197074059495957095386294457, phi_thirtyFourAF_40197074059495957095386294458, phi_thirtyFourAF_40197074059495957095386294459,
    phi_thirtyFourAF_40197074059495957095386294460, phi_thirtyFourAF_40197074059495957095386294461, phi_thirtyFourAF_40197074059495957095386294462,
    phi_thirtyFourAF_40197074059495957095386294463, phi_thirtyFourAF_40197074059495957095386294464, phi_thirtyFourAF_40197074059495957095386294465,
    phi_thirtyFourAF_40197074059495957095386294466, phi_thirtyFourAF_40197074059495957095386294467, phi_thirtyFourAF_40197074059495957095386294468,
    phi_thirtyFourAF_40197074059495957095386294469, phi_thirtyFourAF_40197074059495957095386294470, phi_thirtyFourAF_40197074059495957095386294471,
    phi_thirtyFourAF_40197074059495957095386294472, phi_thirtyFourAF_40197074059495957095386294473, phi_thirtyFourAF_40197074059495957095386294474,
    phi_thirtyFourAF_40197074059495957095386294475, phi_thirtyFourAF_40197074059495957095386294476, phi_thirtyFourAF_40197074059495957095386294477,
    phi_thirtyFourAF_40197074059495957095386294478, phi_thirtyFourAF_40197074059495957095386294479, phi_thirtyFourAF_40197074059495957095386294480,
    phi_thirtyFourAF_40197074059495957095386294481, phi_thirtyFourAF_40197074059495957095386294482, phi_thirtyFourAF_40197074059495957095386294483,
    phi_thirtyFourAF_40197074059495957095386294484, phi_thirtyFourAF_40197074059495957095386294485, phi_thirtyFourAF_40197074059495957095386294486,
    phi_thirtyFourAF_40197074059495957095386294487, phi_thirtyFourAF_40197074059495957095386294488, phi_thirtyFourAF_40197074059495957095386294489,
    phi_thirtyFourAF_40197074059495957095386294490, phi_thirtyFourAF_40197074059495957095386294491, phi_thirtyFourAF_40197074059495957095386294492,
    phi_thirtyFourAF_40197074059495957095386294493, phi_thirtyFourAF_40197074059495957095386294494, phi_thirtyFourAF_40197074059495957095386294495,
    phi_thirtyFourAF_40197074059495957095386294496, phi_thirtyFourAF_40197074059495957095386294497, phi_thirtyFourAF_40197074059495957095386294498,
    phi_thirtyFourAF_40197074059495957095386294499]

end TotientTailPeriodKiller
end Erdos249257
