import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtyFBFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyFBFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyFBFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyFBFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyFBFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyFBFastPow a n * oneHundredSixtyFBFastPow a n * a else oneHundredSixtyFBFastPow a n * oneHundredSixtyFBFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyFB_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtyFB_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtyFB_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtyFB_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtyFB_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtyFB_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtyFB_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtyFB_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtyFB_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtyFB_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtyFB_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtyFB_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtyFB_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtyFB_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtyFB_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtyFB_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtyFB_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtyFB_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtyFB_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtyFB_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtyFB_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtyFB_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtyFB_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtyFB_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtyFB_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtyFB_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtyFB_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtyFB_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtyFB_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtyFB_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtyFB_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtyFB_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtyFB_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtyFB_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtyFB_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixtyFB_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtyFB_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtyFB_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtyFB_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtyFB_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtyFB_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSixtyFB_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtyFB_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixtyFB_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtyFB_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixtyFB_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtyFB_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSixtyFB_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixtyFB_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtyFB_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixtyFB_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixtyFB_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixtyFB_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtyFB_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixtyFB_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSixtyFB_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtyFB_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixtyFB_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSixtyFB_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixtyFB_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixtyFB_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSixtyFB_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixtyFB_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredSixtyFB_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredSixtyFB_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSixtyFB_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixtyFB_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixtyFB_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSixtyFB_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixtyFB_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredSixtyFB_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSixtyFB_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixtyFB_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSixtyFB_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSixtyFB_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredSixtyFB_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixtyFB_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredSixtyFB_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSixtyFB_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixtyFB_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredSixtyFB_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredSixtyFB_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSixtyFB_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredSixtyFB_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredSixtyFB_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredSixtyFB_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSixtyFB_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredSixtyFB_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredSixtyFB_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredSixtyFB_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtyFB_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSixtyFB_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredSixtyFB_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredSixtyFB_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredSixtyFB_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSixtyFB_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredSixtyFB_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredSixtyFB_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSixtyFB_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredSixtyFB_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredSixtyFB_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredSixtyFB_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredSixtyFB_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredSixtyFB_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredSixtyFB_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredSixtyFB_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredSixtyFB_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredSixtyFB_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredSixtyFB_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredSixtyFB_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredSixtyFB_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredSixtyFB_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredSixtyFB_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredSixtyFB_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredSixtyFB_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredSixtyFB_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredSixtyFB_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredSixtyFB_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredSixtyFB_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredSixtyFB_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredSixtyFB_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredSixtyFB_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredSixtyFB_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredSixtyFB_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredSixtyFB_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredSixtyFB_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredSixtyFB_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredSixtyFB_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredSixtyFB_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredSixtyFB_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_oneHundredSixtyFB_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredSixtyFB_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredSixtyFB_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_oneHundredSixtyFB_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredSixtyFB_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredSixtyFB_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_oneHundredSixtyFB_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredSixtyFB_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredSixtyFB_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredSixtyFB_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredSixtyFB_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredSixtyFB_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_oneHundredSixtyFB_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredSixtyFB_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredSixtyFB_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_oneHundredSixtyFB_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_oneHundredSixtyFB_3947 : Nat.Prime 3947 := by norm_num

private theorem prime_oneHundredSixtyFB_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredSixtyFB_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_oneHundredSixtyFB_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredSixtyFB_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredSixtyFB_4327 : Nat.Prime 4327 := by norm_num

private theorem prime_oneHundredSixtyFB_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_oneHundredSixtyFB_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_oneHundredSixtyFB_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_oneHundredSixtyFB_4637 : Nat.Prime 4637 := by norm_num

private theorem prime_oneHundredSixtyFB_4969 : Nat.Prime 4969 := by norm_num

private theorem prime_oneHundredSixtyFB_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredSixtyFB_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_oneHundredSixtyFB_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredSixtyFB_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_oneHundredSixtyFB_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredSixtyFB_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_oneHundredSixtyFB_5843 : Nat.Prime 5843 := by norm_num

private theorem prime_oneHundredSixtyFB_6133 : Nat.Prime 6133 := by norm_num

private theorem prime_oneHundredSixtyFB_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_oneHundredSixtyFB_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_oneHundredSixtyFB_6857 : Nat.Prime 6857 := by norm_num

private theorem prime_oneHundredSixtyFB_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredSixtyFB_7741 : Nat.Prime 7741 := by norm_num

private theorem prime_oneHundredSixtyFB_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_oneHundredSixtyFB_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_oneHundredSixtyFB_8011 : Nat.Prime 8011 := by norm_num

private theorem prime_oneHundredSixtyFB_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredSixtyFB_8311 : Nat.Prime 8311 := by norm_num

private theorem prime_oneHundredSixtyFB_8543 : Nat.Prime 8543 := by norm_num

private theorem prime_oneHundredSixtyFB_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_oneHundredSixtyFB_9377 : Nat.Prime 9377 := by norm_num

private theorem prime_oneHundredSixtyFB_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_oneHundredSixtyFB_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_oneHundredSixtyFB_9631 : Nat.Prime 9631 := by norm_num

private theorem prime_oneHundredSixtyFB_9697 : Nat.Prime 9697 := by norm_num

private theorem prime_oneHundredSixtyFB_9739 : Nat.Prime 9739 := by norm_num

private theorem prime_oneHundredSixtyFB_10037 : Nat.Prime 10037 := by norm_num

private theorem prime_oneHundredSixtyFB_10613 : Nat.Prime 10613 := by norm_num

private theorem prime_oneHundredSixtyFB_10667 : Nat.Prime 10667 := by norm_num

private theorem prime_oneHundredSixtyFB_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_oneHundredSixtyFB_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredSixtyFB_11497 : Nat.Prime 11497 := by norm_num

private theorem prime_oneHundredSixtyFB_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredSixtyFB_11927 : Nat.Prime 11927 := by norm_num

private theorem prime_oneHundredSixtyFB_11987 : Nat.Prime 11987 := by norm_num

private theorem prime_oneHundredSixtyFB_12401 : Nat.Prime 12401 := by norm_num

private theorem prime_oneHundredSixtyFB_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredSixtyFB_12919 : Nat.Prime 12919 := by norm_num

private theorem prime_oneHundredSixtyFB_13003 : Nat.Prime 13003 := by norm_num

private theorem prime_oneHundredSixtyFB_13751 : Nat.Prime 13751 := by norm_num

private theorem prime_oneHundredSixtyFB_14419 : Nat.Prime 14419 := by norm_num

private theorem prime_oneHundredSixtyFB_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredSixtyFB_14713 : Nat.Prime 14713 := by norm_num

private theorem prime_oneHundredSixtyFB_15227 : Nat.Prime 15227 := by norm_num

private theorem prime_oneHundredSixtyFB_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredSixtyFB_15439 : Nat.Prime 15439 := by norm_num

private theorem prime_oneHundredSixtyFB_15817 : Nat.Prime 15817 := by norm_num

private theorem prime_oneHundredSixtyFB_16519 : Nat.Prime 16519 := by norm_num

private theorem prime_oneHundredSixtyFB_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtyFB_17657 : Nat.Prime 17657 := by norm_num

private theorem prime_oneHundredSixtyFB_17791 : Nat.Prime 17791 := by norm_num

private theorem prime_oneHundredSixtyFB_19391 : Nat.Prime 19391 := by norm_num

private theorem prime_oneHundredSixtyFB_19471 : Nat.Prime 19471 := by norm_num

private theorem prime_oneHundredSixtyFB_19609 : Nat.Prime 19609 := by norm_num

private theorem prime_oneHundredSixtyFB_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtyFB_21017 : Nat.Prime 21017 := by norm_num

private theorem prime_oneHundredSixtyFB_21143 : Nat.Prime 21143 := by norm_num

private theorem prime_oneHundredSixtyFB_21859 : Nat.Prime 21859 := by norm_num

private theorem prime_oneHundredSixtyFB_22307 : Nat.Prime 22307 := by norm_num

private theorem prime_oneHundredSixtyFB_22901 : Nat.Prime 22901 := by norm_num

private theorem prime_oneHundredSixtyFB_23057 : Nat.Prime 23057 := by norm_num

private theorem prime_oneHundredSixtyFB_23209 : Nat.Prime 23209 := by norm_num

private theorem prime_oneHundredSixtyFB_24229 : Nat.Prime 24229 := by norm_num

private theorem prime_oneHundredSixtyFB_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredSixtyFB_25409 : Nat.Prime 25409 := by norm_num

private theorem prime_oneHundredSixtyFB_25471 : Nat.Prime 25471 := by norm_num

private theorem prime_oneHundredSixtyFB_25667 : Nat.Prime 25667 := by norm_num

private theorem prime_oneHundredSixtyFB_26947 : Nat.Prime 26947 := by norm_num

private theorem prime_oneHundredSixtyFB_28607 : Nat.Prime 28607 := by norm_num

private theorem prime_oneHundredSixtyFB_30637 : Nat.Prime 30637 := by norm_num

private theorem prime_oneHundredSixtyFB_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredSixtyFB_31817 : Nat.Prime 31817 := by norm_num

private theorem prime_oneHundredSixtyFB_32537 : Nat.Prime 32537 := by norm_num

private theorem prime_oneHundredSixtyFB_32969 : Nat.Prime 32969 := by norm_num

private theorem prime_oneHundredSixtyFB_32999 : Nat.Prime 32999 := by norm_num

private theorem prime_oneHundredSixtyFB_33359 : Nat.Prime 33359 := by norm_num

private theorem prime_oneHundredSixtyFB_33589 : Nat.Prime 33589 := by norm_num

private theorem prime_oneHundredSixtyFB_34807 : Nat.Prime 34807 := by norm_num

private theorem prime_oneHundredSixtyFB_35533 : Nat.Prime 35533 := by norm_num

private theorem prime_oneHundredSixtyFB_36209 : Nat.Prime 36209 := by norm_num

private theorem prime_oneHundredSixtyFB_37309 : Nat.Prime 37309 := by norm_num

private theorem prime_oneHundredSixtyFB_38011 : Nat.Prime 38011 := by norm_num

private theorem prime_oneHundredSixtyFB_38153 : Nat.Prime 38153 := by norm_num

private theorem prime_oneHundredSixtyFB_38639 : Nat.Prime 38639 := by norm_num

private theorem prime_oneHundredSixtyFB_39607 : Nat.Prime 39607 := by norm_num

private theorem prime_oneHundredSixtyFB_42863 : Nat.Prime 42863 := by norm_num

private theorem prime_oneHundredSixtyFB_46819 : Nat.Prime 46819 := by norm_num

private theorem prime_oneHundredSixtyFB_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredSixtyFB_49481 : Nat.Prime 49481 := by norm_num

private theorem prime_oneHundredSixtyFB_49823 : Nat.Prime 49823 := by norm_num

private theorem prime_oneHundredSixtyFB_50929 : Nat.Prime 50929 := by norm_num

private theorem prime_oneHundredSixtyFB_51827 : Nat.Prime 51827 := by norm_num

private theorem prime_oneHundredSixtyFB_52561 : Nat.Prime 52561 := by norm_num

private theorem prime_oneHundredSixtyFB_54449 : Nat.Prime 54449 := by norm_num

private theorem prime_oneHundredSixtyFB_55987 : Nat.Prime 55987 := by norm_num

private theorem prime_oneHundredSixtyFB_56489 : Nat.Prime 56489 := by norm_num

private theorem prime_oneHundredSixtyFB_60887 : Nat.Prime 60887 := by norm_num

private theorem prime_oneHundredSixtyFB_62731 : Nat.Prime 62731 := by norm_num

private theorem prime_oneHundredSixtyFB_63353 : Nat.Prime 63353 := by norm_num

private theorem prime_oneHundredSixtyFB_64667 : Nat.Prime 64667 := by norm_num

private theorem prime_oneHundredSixtyFB_66067 : Nat.Prime 66067 := by norm_num

private theorem prime_oneHundredSixtyFB_66587 : Nat.Prime 66587 := by norm_num

private theorem prime_oneHundredSixtyFB_69491 : Nat.Prime 69491 := by norm_num

private theorem prime_oneHundredSixtyFB_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredSixtyFB_70201 : Nat.Prime 70201 := by norm_num

private theorem prime_oneHundredSixtyFB_70687 : Nat.Prime 70687 := by norm_num

private theorem prime_oneHundredSixtyFB_71983 : Nat.Prime 71983 := by norm_num

private theorem prime_oneHundredSixtyFB_71999 : Nat.Prime 71999 := by norm_num

private theorem prime_oneHundredSixtyFB_72959 : Nat.Prime 72959 := by norm_num

private theorem prime_oneHundredSixtyFB_73387 : Nat.Prime 73387 := by norm_num

private theorem prime_oneHundredSixtyFB_76423 : Nat.Prime 76423 := by norm_num

private theorem prime_oneHundredSixtyFB_78059 : Nat.Prime 78059 := by norm_num

private theorem prime_oneHundredSixtyFB_80107 : Nat.Prime 80107 := by norm_num

private theorem prime_oneHundredSixtyFB_86161 : Nat.Prime 86161 := by norm_num

private theorem prime_oneHundredSixtyFB_87643 : Nat.Prime 87643 := by norm_num

private theorem prime_oneHundredSixtyFB_89009 : Nat.Prime 89009 := by norm_num

private theorem prime_oneHundredSixtyFB_90011 : Nat.Prime 90011 := by norm_num

private theorem prime_oneHundredSixtyFB_96697 : Nat.Prime 96697 := by norm_num

private theorem prime_oneHundredSixtyFB_98669 : Nat.Prime 98669 := by norm_num

private theorem prime_oneHundredSixtyFB_111637 : Nat.Prime 111637 := by norm_num

private theorem prime_oneHundredSixtyFB_111827 : Nat.Prime 111827 := by norm_num

private theorem prime_oneHundredSixtyFB_112997 : Nat.Prime 112997 := by norm_num

private theorem prime_oneHundredSixtyFB_113363 : Nat.Prime 113363 := by norm_num

private theorem prime_oneHundredSixtyFB_122327 : Nat.Prime 122327 := by norm_num

private theorem prime_oneHundredSixtyFB_123373 : Nat.Prime 123373 := by norm_num

private theorem prime_oneHundredSixtyFB_131441 : Nat.Prime 131441 := by norm_num

private theorem prime_oneHundredSixtyFB_141871 : Nat.Prime 141871 := by norm_num

private theorem prime_oneHundredSixtyFB_144103 : Nat.Prime 144103 := by norm_num

private theorem prime_oneHundredSixtyFB_144667 : Nat.Prime 144667 := by norm_num

private theorem prime_oneHundredSixtyFB_145349 : Nat.Prime 145349 := by norm_num

private theorem prime_oneHundredSixtyFB_150107 : Nat.Prime 150107 := by norm_num

private theorem prime_oneHundredSixtyFB_151817 : Nat.Prime 151817 := by norm_num

private theorem prime_oneHundredSixtyFB_162391 : Nat.Prime 162391 := by norm_num

private theorem prime_oneHundredSixtyFB_165673 : Nat.Prime 165673 := by norm_num

private theorem prime_oneHundredSixtyFB_170347 : Nat.Prime 170347 := by norm_num

private theorem prime_oneHundredSixtyFB_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredSixtyFB_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtyFB_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredSixtyFB_188249 : Nat.Prime 188249 := by norm_num

private theorem prime_oneHundredSixtyFB_191123 : Nat.Prime 191123 := by norm_num

private theorem prime_oneHundredSixtyFB_196201 : Nat.Prime 196201 := by norm_num

private theorem prime_oneHundredSixtyFB_202931 : Nat.Prime 202931 := by norm_num

private theorem prime_oneHundredSixtyFB_204719 : Nat.Prime 204719 := by norm_num

private theorem prime_oneHundredSixtyFB_208367 : Nat.Prime 208367 := by norm_num

private theorem prime_oneHundredSixtyFB_210031 : Nat.Prime 210031 := by norm_num

private theorem prime_oneHundredSixtyFB_218641 : Nat.Prime 218641 := by norm_num

private theorem prime_oneHundredSixtyFB_227093 : Nat.Prime 227093 := by norm_num

private theorem prime_oneHundredSixtyFB_229739 : Nat.Prime 229739 := by norm_num

private theorem prime_oneHundredSixtyFB_232153 : Nat.Prime 232153 := by norm_num

private theorem prime_oneHundredSixtyFB_235397 : Nat.Prime 235397 := by norm_num

private theorem prime_oneHundredSixtyFB_240209 : Nat.Prime 240209 := by norm_num

private theorem prime_oneHundredSixtyFB_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredSixtyFB_254731 : Nat.Prime 254731 := by norm_num

private theorem prime_oneHundredSixtyFB_266183 : Nat.Prime 266183 := by norm_num

private theorem prime_oneHundredSixtyFB_266719 : Nat.Prime 266719 := by norm_num

private theorem prime_oneHundredSixtyFB_274777 : Nat.Prime 274777 := by norm_num

private theorem prime_oneHundredSixtyFB_279029 : Nat.Prime 279029 := by norm_num

private theorem prime_oneHundredSixtyFB_279553 : Nat.Prime 279553 := by norm_num

private theorem prime_oneHundredSixtyFB_286199 : Nat.Prime 286199 := by norm_num

private theorem prime_oneHundredSixtyFB_306457 : Nat.Prime 306457 := by norm_num

private theorem prime_oneHundredSixtyFB_328429 : Nat.Prime 328429 := by norm_num

private theorem prime_oneHundredSixtyFB_333787 : Nat.Prime 333787 := by norm_num

private theorem prime_oneHundredSixtyFB_339613 : Nat.Prime 339613 := by norm_num

private theorem prime_oneHundredSixtyFB_350521 : Nat.Prime 350521 := by norm_num

private theorem prime_oneHundredSixtyFB_353149 : Nat.Prime 353149 := by norm_num

private theorem prime_oneHundredSixtyFB_361787 : Nat.Prime 361787 := by norm_num

private theorem prime_oneHundredSixtyFB_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredSixtyFB_375563 : Nat.Prime 375563 := by norm_num

private theorem prime_oneHundredSixtyFB_390389 : Nat.Prime 390389 := by norm_num

private theorem prime_oneHundredSixtyFB_408211 : Nat.Prime 408211 := by norm_num

private theorem prime_oneHundredSixtyFB_417023 : Nat.Prime 417023 := by norm_num

private theorem prime_oneHundredSixtyFB_454151 : Nat.Prime 454151 := by norm_num

private theorem prime_oneHundredSixtyFB_456151 : Nat.Prime 456151 := by norm_num

private theorem prime_oneHundredSixtyFB_482501 : Nat.Prime 482501 := by norm_num

private theorem prime_oneHundredSixtyFB_489911 : Nat.Prime 489911 := by norm_num

private theorem prime_oneHundredSixtyFB_527581 : Nat.Prime 527581 := by norm_num

private theorem prime_oneHundredSixtyFB_537583 : Nat.Prime 537583 := by norm_num

private theorem prime_oneHundredSixtyFB_576469 : Nat.Prime 576469 := by norm_num

private theorem prime_oneHundredSixtyFB_587107 : Nat.Prime 587107 := by norm_num

private theorem prime_oneHundredSixtyFB_602411 : Nat.Prime 602411 := by norm_num

private theorem prime_oneHundredSixtyFB_603739 : Nat.Prime 603739 := by norm_num

private theorem prime_oneHundredSixtyFB_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredSixtyFB_646669 : Nat.Prime 646669 := by norm_num

private theorem prime_oneHundredSixtyFB_667081 : Nat.Prime 667081 := by norm_num

private theorem prime_oneHundredSixtyFB_676337 : Nat.Prime 676337 := by norm_num

private theorem prime_oneHundredSixtyFB_701447 : Nat.Prime 701447 := by norm_num

private theorem prime_oneHundredSixtyFB_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredSixtyFB_705769 : Nat.Prime 705769 := by norm_num

private theorem prime_oneHundredSixtyFB_723133 : Nat.Prime 723133 := by norm_num

private theorem prime_oneHundredSixtyFB_785461 : Nat.Prime 785461 := by norm_num

private theorem prime_oneHundredSixtyFB_794191 : Nat.Prime 794191 := by norm_num

private theorem prime_oneHundredSixtyFB_846733 : Nat.Prime 846733 := by norm_num

private theorem prime_oneHundredSixtyFB_849593 : Nat.Prime 849593 := by norm_num

private theorem prime_oneHundredSixtyFB_1092307 : Nat.Prime 1092307 := by norm_num

private theorem prime_oneHundredSixtyFB_1116419 : Nat.Prime 1116419 := by norm_num

private theorem prime_oneHundredSixtyFB_1174021 : Nat.Prime 1174021 := by norm_num

private theorem prime_oneHundredSixtyFB_1187363 : Nat.Prime 1187363 := by norm_num

private theorem prime_oneHundredSixtyFB_1233371 : Nat.Prime 1233371 := by norm_num

private theorem prime_oneHundredSixtyFB_1282451 : Nat.Prime 1282451 := by norm_num

private theorem prime_oneHundredSixtyFB_1363031 : Nat.Prime 1363031 := by norm_num

private theorem prime_oneHundredSixtyFB_1400947 : Nat.Prime 1400947 := by norm_num

private theorem prime_oneHundredSixtyFB_1430711 : Nat.Prime 1430711 := by norm_num

private theorem prime_oneHundredSixtyFB_1443697 : Nat.Prime 1443697 := by norm_num

private theorem prime_oneHundredSixtyFB_1445117 : Nat.Prime 1445117 := by norm_num

private theorem prime_oneHundredSixtyFB_1447583 : Nat.Prime 1447583 := by norm_num

private theorem prime_oneHundredSixtyFB_1536649 : Nat.Prime 1536649 := by norm_num

private theorem prime_oneHundredSixtyFB_1545121 : Nat.Prime 1545121 := by norm_num

private theorem prime_oneHundredSixtyFB_1545653 : Nat.Prime 1545653 := by norm_num

private theorem prime_oneHundredSixtyFB_1720217 : Nat.Prime 1720217 := by norm_num

private theorem prime_oneHundredSixtyFB_1732967 : Nat.Prime 1732967 := by norm_num

private theorem prime_oneHundredSixtyFB_1887283 : Nat.Prime 1887283 := by norm_num

private theorem prime_oneHundredSixtyFB_2035379 : Nat.Prime 2035379 := by norm_num

private theorem prime_oneHundredSixtyFB_2094779 : Nat.Prime 2094779 := by norm_num

private theorem prime_oneHundredSixtyFB_2101129 : Nat.Prime 2101129 := by norm_num

private theorem prime_oneHundredSixtyFB_2126441 : Nat.Prime 2126441 := by norm_num

private theorem prime_oneHundredSixtyFB_2174941 : Nat.Prime 2174941 := by norm_num

private theorem prime_oneHundredSixtyFB_2276699 : Nat.Prime 2276699 := by norm_num

private theorem prime_oneHundredSixtyFB_2347823 : Nat.Prime 2347823 := by norm_num

private theorem prime_oneHundredSixtyFB_2500999 : Nat.Prime 2500999 := by norm_num

private theorem prime_oneHundredSixtyFB_2679697 : Nat.Prime 2679697 := by norm_num

private theorem prime_oneHundredSixtyFB_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredSixtyFB_2823221 : Nat.Prime 2823221 := by norm_num

private theorem prime_oneHundredSixtyFB_2829383 : Nat.Prime 2829383 := by norm_num

private theorem prime_oneHundredSixtyFB_3534379 : Nat.Prime 3534379 := by norm_num

private theorem prime_oneHundredSixtyFB_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredSixtyFB_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredSixtyFB_3613349 : Nat.Prime 3613349 := by norm_num

private theorem prime_oneHundredSixtyFB_3616147 : Nat.Prime 3616147 := by norm_num

private theorem prime_oneHundredSixtyFB_3780113 : Nat.Prime 3780113 := by norm_num

private theorem prime_oneHundredSixtyFB_3858037 : Nat.Prime 3858037 := by norm_num

private theorem prime_oneHundredSixtyFB_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredSixtyFB_4460767 : Nat.Prime 4460767 := by norm_num

private theorem prime_oneHundredSixtyFB_4542203 : Nat.Prime 4542203 := by norm_num

private theorem prime_oneHundredSixtyFB_4641907 : Nat.Prime 4641907 := by norm_num

private theorem prime_oneHundredSixtyFB_4744163 : Nat.Prime 4744163 := by norm_num

private theorem prime_oneHundredSixtyFB_5534569 : Nat.Prime 5534569 := by norm_num

private theorem prime_oneHundredSixtyFB_5580977 : Nat.Prime 5580977 := by norm_num

private theorem prime_oneHundredSixtyFB_5813989 : Nat.Prime 5813989 := by norm_num

private theorem prime_oneHundredSixtyFB_6240749 : Nat.Prime 6240749 := by norm_num

private theorem prime_oneHundredSixtyFB_6318211 : Nat.Prime 6318211 := by norm_num

private theorem prime_oneHundredSixtyFB_6881383 : Nat.Prime 6881383 := by norm_num

private theorem prime_oneHundredSixtyFB_7151687 : Nat.Prime 7151687 := by norm_num

private theorem prime_oneHundredSixtyFB_7652783 : Nat.Prime 7652783 := by norm_num

private theorem prime_oneHundredSixtyFB_8593597 : Nat.Prime 8593597 := by norm_num

private theorem prime_oneHundredSixtyFB_9365437 : Nat.Prime 9365437 := by norm_num

private theorem prime_oneHundredSixtyFB_9554807 : Nat.Prime 9554807 := by norm_num

private theorem prime_oneHundredSixtyFB_9678611 : Nat.Prime 9678611 := by norm_num

private theorem prime_oneHundredSixtyFB_10058177 : Nat.Prime 10058177 := by norm_num

private theorem prime_oneHundredSixtyFB_10072081 : Nat.Prime 10072081 := by norm_num

private theorem prime_oneHundredSixtyFB_10163389 : Nat.Prime 10163389 := by norm_num

private theorem prime_oneHundredSixtyFB_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtyFB_11197063 : Nat.Prime 11197063 := by norm_num

private theorem prime_oneHundredSixtyFB_11292583 : Nat.Prime 11292583 := by norm_num

private theorem prime_oneHundredSixtyFB_11333351 : Nat.Prime 11333351 := by norm_num

private theorem prime_oneHundredSixtyFB_13511921 : Nat.Prime 13511921 := by norm_num

private theorem prime_oneHundredSixtyFB_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredSixtyFB_14498333 : Nat.Prime 14498333 := by norm_num

private theorem prime_oneHundredSixtyFB_14642821 : Nat.Prime 14642821 := by norm_num

private theorem prime_oneHundredSixtyFB_16432069 : Nat.Prime 16432069 := by norm_num

private theorem prime_oneHundredSixtyFB_16616983 : Nat.Prime 16616983 := by norm_num

private theorem prime_oneHundredSixtyFB_17435513 : Nat.Prime 17435513 := by norm_num

private theorem prime_oneHundredSixtyFB_17789069 : Nat.Prime 17789069 := by norm_num

private theorem prime_oneHundredSixtyFB_17957579 : Nat.Prime 17957579 := by norm_num

private theorem prime_oneHundredSixtyFB_18151967 : Nat.Prime 18151967 := by norm_num

private theorem prime_oneHundredSixtyFB_19156283 : Nat.Prime 19156283 := by norm_num

private theorem prime_oneHundredSixtyFB_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredSixtyFB_20589017 : Nat.Prime 20589017 := by norm_num

private theorem prime_oneHundredSixtyFB_20846261 : Nat.Prime 20846261 := by norm_num

private theorem prime_oneHundredSixtyFB_21882703 : Nat.Prime 21882703 := by norm_num

private theorem prime_oneHundredSixtyFB_25028651 : Nat.Prime 25028651 := by norm_num

private theorem prime_oneHundredSixtyFB_25411709 : Nat.Prime 25411709 := by norm_num

private theorem prime_oneHundredSixtyFB_26655217 : Nat.Prime 26655217 := by norm_num

private theorem prime_oneHundredSixtyFB_29397911 : Nat.Prime 29397911 := by norm_num

private theorem prime_oneHundredSixtyFB_32063099 : Nat.Prime 32063099 := by
  apply lucas_primality 32063099 (2 : ZMod 32063099)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (202931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (202931, 1)] : List FactorBlock).map factorBlockValue).prod) = 32063099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_79
      · exact prime_oneHundredSixtyFB_202931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32063099) ^ 16031549 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32063099) ^ 405862 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32063099) ^ 158 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_32276201 : Nat.Prime 32276201 := by
  apply lucas_primality 32276201 (3 : ZMod 32276201)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (17, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (17, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 32276201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32276201) ^ 16138100 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32276201) ^ 6455240 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32276201) ^ 2934200 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32276201) ^ 1898600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32276201) ^ 37400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_33004963 : Nat.Prime 33004963 := by
  apply lucas_primality 33004963 (2 : ZMod 33004963)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (16519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (16519, 1)] : List FactorBlock).map factorBlockValue).prod) = 33004963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_16519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33004963) ^ 16502481 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33004963) ^ 11001654 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33004963) ^ 892026 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33004963) ^ 1998 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_34871027 : Nat.Prime 34871027 := by
  apply lucas_primality 34871027 (2 : ZMod 34871027)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17435513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17435513, 1)] : List FactorBlock).map factorBlockValue).prod) = 34871027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_17435513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34871027) ^ 17435513 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 34871027) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_37172717 : Nat.Prime 37172717 := by
  apply lucas_primality 37172717 (2 : ZMod 37172717)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (53, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (53, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 37172717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_53
      · exact prime_oneHundredSixtyFB_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37172717) ^ 18586358 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 37172717) ^ 5310388 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 37172717) ^ 1004668 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 37172717) ^ 701372 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 37172717) ^ 54908 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_37711889 : Nat.Prime 37711889 := by
  apply lucas_primality 37711889 (3 : ZMod 37711889)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (127, 1), (277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (127, 1), (277, 1)] : List FactorBlock).map factorBlockValue).prod) = 37711889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_67
      · exact prime_oneHundredSixtyFB_127
      · exact prime_oneHundredSixtyFB_277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37711889) ^ 18855944 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37711889) ^ 562864 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37711889) ^ 296944 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37711889) ^ 136144 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_43813733 : Nat.Prime 43813733 := by
  apply lucas_primality 43813733 (2 : ZMod 43813733)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (254731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (254731, 1)] : List FactorBlock).map factorBlockValue).prod) = 43813733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_254731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43813733) ^ 21906866 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 43813733) ^ 1018924 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 43813733) ^ 172 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_44788253 : Nat.Prime 44788253 := by
  apply lucas_primality 44788253 (2 : ZMod 44788253)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11197063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11197063, 1)] : List FactorBlock).map factorBlockValue).prod) = 44788253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11197063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 44788253) ^ 22394126 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44788253) ^ 4 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_45994279 : Nat.Prime 45994279 := by
  apply lucas_primality 45994279 (3 : ZMod 45994279)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) = 45994279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_63353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45994279) ^ 22997139 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 15331426 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 4181298 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 726 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_46501019 : Nat.Prime 46501019 := by
  apply lucas_primality 46501019 (2 : ZMod 46501019)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) = 46501019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_71983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46501019) ^ 23250509 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2735354 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2447422 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 646 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_41
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_50038073 : Nat.Prime 50038073 := by
  apply lucas_primality 50038073 (3 : ZMod 50038073)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (52561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (52561, 1)] : List FactorBlock).map factorBlockValue).prod) = 50038073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_52561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50038073) ^ 25019036 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 50038073) ^ 7148296 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 50038073) ^ 2943416 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 50038073) ^ 952 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_55413389 : Nat.Prime 55413389 := by
  apply lucas_primality 55413389 (2 : ZMod 55413389)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55413389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_179
      · exact prime_oneHundredSixtyFB_193
      · exact prime_oneHundredSixtyFB_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55413389) ^ 27706694 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 309572 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 287116 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 138188 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_57001003 : Nat.Prime 57001003 := by
  apply lucas_primality 57001003 (3 : ZMod 57001003)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (306457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (306457, 1)] : List FactorBlock).map factorBlockValue).prod) = 57001003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_31
      · exact prime_oneHundredSixtyFB_306457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57001003) ^ 28500501 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 57001003) ^ 19000334 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 57001003) ^ 1838742 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 57001003) ^ 186 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_57536287 : Nat.Prime 57536287 := by
  apply lucas_primality 57536287 (6 : ZMod 57536287)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (30637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (30637, 1)] : List FactorBlock).map factorBlockValue).prod) = 57536287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_313
      · exact prime_oneHundredSixtyFB_30637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57536287) ^ 28768143 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 57536287) ^ 19178762 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 57536287) ^ 183822 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 57536287) ^ 1878 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_59437061 : Nat.Prime 59437061 := by
  apply lucas_primality 59437061 (2 : ZMod 59437061)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (157, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (157, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 59437061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_157
      · exact prime_oneHundredSixtyFB_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59437061) ^ 29718530 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59437061) ^ 11887412 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59437061) ^ 2584220 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59437061) ^ 378580 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59437061) ^ 72220 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_1811
      · exact prime_oneHundredSixtyFB_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_69967783 : Nat.Prime 69967783 := by
  apply lucas_primality 69967783 (5 : ZMod 69967783)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (733, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (733, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 69967783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_733
      · exact prime_oneHundredSixtyFB_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 69967783) ^ 34983891 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 69967783) ^ 23322594 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 69967783) ^ 95454 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 69967783) ^ 13194 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_72126287 : Nat.Prime 72126287 := by
  apply lucas_primality 72126287 (5 : ZMod 72126287)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3719, 1), (9697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3719, 1), (9697, 1)] : List FactorBlock).map factorBlockValue).prod) = 72126287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3719
      · exact prime_oneHundredSixtyFB_9697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 72126287) ^ 36063143 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 72126287) ^ 19394 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 72126287) ^ 7438 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_75843941 : Nat.Prime 75843941 := by
  apply lucas_primality 75843941 (2 : ZMod 75843941)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (263, 1), (14419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (263, 1), (14419, 1)] : List FactorBlock).map factorBlockValue).prod) = 75843941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_263
      · exact prime_oneHundredSixtyFB_14419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75843941) ^ 37921970 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75843941) ^ 15168788 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75843941) ^ 288380 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75843941) ^ 5260 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_89785217 : Nat.Prime 89785217 := by
  apply lucas_primality 89785217 (3 : ZMod 89785217)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (701447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (701447, 1)] : List FactorBlock).map factorBlockValue).prod) = 89785217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_701447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 89785217) ^ 44892608 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 89785217) ^ 128 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_91568473 : Nat.Prime 91568473 := by
  apply lucas_primality 91568473 (5 : ZMod 91568473)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (64667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (64667, 1)] : List FactorBlock).map factorBlockValue).prod) = 91568473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_59
      · exact prime_oneHundredSixtyFB_64667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91568473) ^ 45784236 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 91568473) ^ 30522824 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 91568473) ^ 1552008 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 91568473) ^ 1416 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_98623627 : Nat.Prime 98623627 := by
  apply lucas_primality 98623627 (2 : ZMod 98623627)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1721, 1), (9551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1721, 1), (9551, 1)] : List FactorBlock).map factorBlockValue).prod) = 98623627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_1721
      · exact prime_oneHundredSixtyFB_9551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 98623627) ^ 49311813 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 98623627) ^ 32874542 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 98623627) ^ 57306 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 98623627) ^ 10326 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_100076147 : Nat.Prime 100076147 := by
  apply lucas_primality 100076147 (2 : ZMod 100076147)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (50038073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (50038073, 1)] : List FactorBlock).map factorBlockValue).prod) = 100076147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_50038073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 100076147) ^ 50038073 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 100076147) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_100123619 : Nat.Prime 100123619 := by
  apply lucas_primality 100123619 (2 : ZMod 100123619)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7151687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7151687, 1)] : List FactorBlock).map factorBlockValue).prod) = 100123619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_7151687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 100123619) ^ 50061809 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 100123619) ^ 14303374 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 100123619) ^ 14 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_104406371 : Nat.Prime 104406371 := by
  apply lucas_primality 104406371 (6 : ZMod 104406371)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (223, 1), (46819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (223, 1), (46819, 1)] : List FactorBlock).map factorBlockValue).prod) = 104406371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_223
      · exact prime_oneHundredSixtyFB_46819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 104406371) ^ 52203185 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 104406371) ^ 20881274 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 104406371) ^ 468190 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 104406371) ^ 2230 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_105211543 : Nat.Prime 105211543 := by
  apply lucas_primality 105211543 (3 : ZMod 105211543)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (240209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (240209, 1)] : List FactorBlock).map factorBlockValue).prod) = 105211543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_73
      · exact prime_oneHundredSixtyFB_240209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 105211543) ^ 52605771 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211543) ^ 35070514 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211543) ^ 1441254 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211543) ^ 438 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_110589257 : Nat.Prime 110589257 := by
  apply lucas_primality 110589257 (3 : ZMod 110589257)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (233, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (233, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 110589257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_79
      · exact prime_oneHundredSixtyFB_233
      · exact prime_oneHundredSixtyFB_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110589257) ^ 55294628 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 110589257) ^ 1399864 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 110589257) ^ 474632 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 110589257) ^ 147256 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_121791431 : Nat.Prime 121791431 := by
  apply lucas_primality 121791431 (11 : ZMod 121791431)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (167, 1), (233, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (167, 1), (233, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 121791431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_167
      · exact prime_oneHundredSixtyFB_233
      · exact prime_oneHundredSixtyFB_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 121791431) ^ 60895715 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 121791431) ^ 24358286 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 121791431) ^ 729290 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 121791431) ^ 522710 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 121791431) ^ 389110 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_131703791 : Nat.Prime 131703791 := by
  apply lucas_primality 131703791 (7 : ZMod 131703791)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (454151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (454151, 1)] : List FactorBlock).map factorBlockValue).prod) = 131703791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_454151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 131703791) ^ 65851895 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 131703791) ^ 26340758 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 131703791) ^ 4541510 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 131703791) ^ 290 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_141965899 : Nat.Prime 141965899 := by
  apply lucas_primality 141965899 (3 : ZMod 141965899)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (353149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (353149, 1)] : List FactorBlock).map factorBlockValue).prod) = 141965899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_67
      · exact prime_oneHundredSixtyFB_353149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 141965899) ^ 70982949 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 141965899) ^ 47321966 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 141965899) ^ 2118894 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 141965899) ^ 402 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_142312553 : Nat.Prime 142312553 := by
  apply lucas_primality 142312553 (3 : ZMod 142312553)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17789069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17789069, 1)] : List FactorBlock).map factorBlockValue).prod) = 142312553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_17789069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 142312553) ^ 71156276 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 142312553) ^ 8 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_145203703 : Nat.Prime 145203703 := by
  apply lucas_primality 145203703 (5 : ZMod 145203703)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (821, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (821, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 145203703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_821
      · exact prime_oneHundredSixtyFB_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 145203703) ^ 72601851 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 145203703) ^ 48401234 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 145203703) ^ 20743386 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 145203703) ^ 176862 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 145203703) ^ 34482 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_150171907 : Nat.Prime 150171907 := by
  apply lucas_primality 150171907 (2 : ZMod 150171907)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (25028651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (25028651, 1)] : List FactorBlock).map factorBlockValue).prod) = 150171907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_25028651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 150171907) ^ 75085953 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 150171907) ^ 50057302 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 150171907) ^ 6 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_151687883 : Nat.Prime 151687883 := by
  apply lucas_primality 151687883 (2 : ZMod 151687883)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (75843941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (75843941, 1)] : List FactorBlock).map factorBlockValue).prod) = 151687883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_75843941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 151687883) ^ 75843941 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 151687883) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_158554247 : Nat.Prime 158554247 := by
  apply lucas_primality 158554247 (5 : ZMod 158554247)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (277, 1), (286199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (277, 1), (286199, 1)] : List FactorBlock).map factorBlockValue).prod) = 158554247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_277
      · exact prime_oneHundredSixtyFB_286199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 158554247) ^ 79277123 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 158554247) ^ 572398 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 158554247) ^ 554 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_166169831 : Nat.Prime 166169831 := by
  apply lucas_primality 166169831 (7 : ZMod 166169831)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (16616983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (16616983, 1)] : List FactorBlock).map factorBlockValue).prod) = 166169831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_16616983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 166169831) ^ 83084915 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 166169831) ^ 33233966 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 166169831) ^ 10 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_169287779 : Nat.Prime 169287779 := by
  apply lucas_primality 169287779 (2 : ZMod 169287779)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (523, 1), (14713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (523, 1), (14713, 1)] : List FactorBlock).map factorBlockValue).prod) = 169287779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_523
      · exact prime_oneHundredSixtyFB_14713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 169287779) ^ 84643889 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 169287779) ^ 15389798 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 169287779) ^ 323686 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 169287779) ^ 11506 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_177115951 : Nat.Prime 177115951 := by
  apply lucas_primality 177115951 (3 : ZMod 177115951)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (11, 1), (11927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (11, 1), (11927, 1)] : List FactorBlock).map factorBlockValue).prod) = 177115951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_11927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 177115951) ^ 88557975 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 177115951) ^ 59038650 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 177115951) ^ 35423190 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 177115951) ^ 16101450 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 177115951) ^ 14850 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_193657207 : Nat.Prime 193657207 := by
  apply lucas_primality 193657207 (3 : ZMod 193657207)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32276201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32276201, 1)] : List FactorBlock).map factorBlockValue).prod) = 193657207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_32276201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193657207) ^ 96828603 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 193657207) ^ 64552402 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 193657207) ^ 6 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_198515441 : Nat.Prime 198515441 := by
  apply lucas_primality 198515441 (3 : ZMod 198515441)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (41, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (41, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) = 198515441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_41
      · exact prime_oneHundredSixtyFB_2087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 198515441) ^ 99257720 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 198515441) ^ 39703088 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 198515441) ^ 6845360 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 198515441) ^ 4841840 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 198515441) ^ 95120 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_229583491 : Nat.Prime 229583491 := by
  apply lucas_primality 229583491 (2 : ZMod 229583491)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7652783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7652783, 1)] : List FactorBlock).map factorBlockValue).prod) = 229583491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7652783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 229583491) ^ 114791745 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 229583491) ^ 76527830 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 229583491) ^ 45916698 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 229583491) ^ 30 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_248129153 : Nat.Prime 248129153 := by
  apply lucas_primality 248129153 (3 : ZMod 248129153)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 248129153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_89
      · exact prime_oneHundredSixtyFB_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 248129153) ^ 124064576 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 10788224 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 2787968 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 262016 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_250155133 : Nat.Prime 250155133 := by
  apply lucas_primality 250155133 (5 : ZMod 250155133)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20846261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20846261, 1)] : List FactorBlock).map factorBlockValue).prod) = 250155133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_20846261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 250155133) ^ 125077566 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 250155133) ^ 83385044 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 250155133) ^ 12 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_266552171 : Nat.Prime 266552171 := by
  apply lucas_primality 266552171 (2 : ZMod 266552171)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) = 266552171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_26655217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 266552171) ^ 133276085 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 53310434 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 10 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_274157269 : Nat.Prime 274157269 := by
  apply lucas_primality 274157269 (2 : ZMod 274157269)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (269, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (269, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) = 274157269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_269
      · exact prime_oneHundredSixtyFB_1103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274157269) ^ 137078634 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 274157269) ^ 91385756 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 274157269) ^ 39165324 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 274157269) ^ 24923388 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 274157269) ^ 1019172 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 274157269) ^ 248556 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_275681563 : Nat.Prime 275681563 := by
  apply lucas_primality 275681563 (2 : ZMod 275681563)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3534379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3534379, 1)] : List FactorBlock).map factorBlockValue).prod) = 275681563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_3534379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 275681563) ^ 137840781 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 275681563) ^ 91893854 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 275681563) ^ 21206274 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 275681563) ^ 78 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_289966661 : Nat.Prime 289966661 := by
  apply lucas_primality 289966661 (3 : ZMod 289966661)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (14498333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (14498333, 1)] : List FactorBlock).map factorBlockValue).prod) = 289966661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_14498333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 289966661) ^ 144983330 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 289966661) ^ 57993332 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 289966661) ^ 20 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_292809137 : Nat.Prime 292809137 := by
  apply lucas_primality 292809137 (3 : ZMod 292809137)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (31, 1), (25667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (31, 1), (25667, 1)] : List FactorBlock).map factorBlockValue).prod) = 292809137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_31
      · exact prime_oneHundredSixtyFB_25667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 292809137) ^ 146404568 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 292809137) ^ 12730832 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 292809137) ^ 9445456 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 292809137) ^ 11408 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_303375767 : Nat.Prime 303375767 := by
  apply lucas_primality 303375767 (5 : ZMod 303375767)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151687883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151687883, 1)] : List FactorBlock).map factorBlockValue).prod) = 303375767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_151687883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 303375767) ^ 151687883 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 303375767) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_12539
      · exact prime_oneHundredSixtyFB_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_418664849 : Nat.Prime 418664849 := by
  apply lucas_primality 418664849 (3 : ZMod 418664849)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (19, 1), (71, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (19, 1), (71, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 418664849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 418664849) ^ 209332424 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 418664849) ^ 59809264 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 418664849) ^ 24627344 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 418664849) ^ 22034992 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 418664849) ^ 5896688 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 418664849) ^ 2568496 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_426471607 : Nat.Prime 426471607 := by
  apply lucas_primality 426471607 (5 : ZMod 426471607)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (19, 1), (113363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (19, 1), (113363, 1)] : List FactorBlock).map factorBlockValue).prod) = 426471607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_113363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 426471607) ^ 213235803 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 426471607) ^ 142157202 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 426471607) ^ 38770146 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 426471607) ^ 22445874 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 426471607) ^ 3762 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_442678111 : Nat.Prime 442678111 := by
  apply lucas_primality 442678111 (3 : ZMod 442678111)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (389, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (389, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) = 442678111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_389
      · exact prime_oneHundredSixtyFB_5419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 442678111) ^ 221339055 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442678111) ^ 147559370 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442678111) ^ 88535622 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442678111) ^ 63239730 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442678111) ^ 1137990 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442678111) ^ 81690 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_502908851 : Nat.Prime 502908851 := by
  apply lucas_primality 502908851 (2 : ZMod 502908851)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (10058177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (10058177, 1)] : List FactorBlock).map factorBlockValue).prod) = 502908851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_10058177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 502908851) ^ 251454425 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 502908851) ^ 100581770 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 502908851) ^ 50 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_545717467 : Nat.Prime 545717467 := by
  apply lucas_primality 545717467 (3 : ZMod 545717467)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (1443697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (1443697, 1)] : List FactorBlock).map factorBlockValue).prod) = 545717467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_1443697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 545717467) ^ 272858733 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 545717467) ^ 181905822 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 545717467) ^ 77959638 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 545717467) ^ 378 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_551561071 : Nat.Prime 551561071 := by
  apply lucas_primality 551561071 (3 : ZMod 551561071)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 2), (50929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 2), (50929, 1)] : List FactorBlock).map factorBlockValue).prod) = 551561071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_50929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 551561071) ^ 275780535 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 551561071) ^ 183853690 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 551561071) ^ 110312214 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 551561071) ^ 29029530 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 551561071) ^ 10830 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_587031281 : Nat.Prime 587031281 := by
  apply lucas_primality 587031281 (3 : ZMod 587031281)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (667081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (667081, 1)] : List FactorBlock).map factorBlockValue).prod) = 587031281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_667081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 587031281) ^ 293515640 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587031281) ^ 117406256 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587031281) ^ 53366480 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587031281) ^ 880 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_615865027 : Nat.Prime 615865027 := by
  apply lucas_primality 615865027 (2 : ZMod 615865027)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (2094779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (2094779, 1)] : List FactorBlock).map factorBlockValue).prod) = 615865027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_2094779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 615865027) ^ 307932513 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 615865027) ^ 205288342 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 615865027) ^ 87980718 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 615865027) ^ 294 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_679311571 : Nat.Prime 679311571 := by
  apply lucas_primality 679311571 (2 : ZMod 679311571)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) = 679311571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_127
      · exact prime_oneHundredSixtyFB_25471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 679311571) ^ 339655785 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 226437190 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 135862314 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 97044510 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 5348910 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 26670 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_711437231 : Nat.Prime 711437231 := by
  apply lucas_primality 711437231 (7 : ZMod 711437231)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (10163389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (10163389, 1)] : List FactorBlock).map factorBlockValue).prod) = 711437231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_10163389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 711437231) ^ 355718615 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 711437231) ^ 142287446 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 711437231) ^ 101633890 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 711437231) ^ 70 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_17203
      · exact prime_oneHundredSixtyFB_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_726266953 : Nat.Prime 726266953 := by
  apply lucas_primality 726266953 (5 : ZMod 726266953)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (23, 1), (29, 1), (71, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (23, 1), (29, 1), (71, 2)] : List FactorBlock).map factorBlockValue).prod) = 726266953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_71
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 726266953) ^ 363133476 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 726266953) ^ 242088984 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 726266953) ^ 31576824 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 726266953) ^ 25043688 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 726266953) ^ 10229112 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_764417231 : Nat.Prime 764417231 := by
  apply lucas_primality 764417231 (7 : ZMod 764417231)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 764417231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_61
      · exact prime_oneHundredSixtyFB_97
      · exact prime_oneHundredSixtyFB_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 764417231) ^ 382208615 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 152883446 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 12531430 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 7880590 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 59170 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_796052281 : Nat.Prime 796052281 := by
  apply lucas_primality 796052281 (7 : ZMod 796052281)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (577, 1), (11497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (577, 1), (11497, 1)] : List FactorBlock).map factorBlockValue).prod) = 796052281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_577
      · exact prime_oneHundredSixtyFB_11497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 796052281) ^ 398026140 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 265350760 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 159210456 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 1379640 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 69240 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_829311991 : Nat.Prime 829311991 := by
  apply lucas_primality 829311991 (6 : ZMod 829311991)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (2126441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (2126441, 1)] : List FactorBlock).map factorBlockValue).prod) = 829311991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_2126441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 829311991) ^ 414655995 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 829311991) ^ 276437330 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 829311991) ^ 165862398 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 829311991) ^ 63793230 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 829311991) ^ 390 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1007208101 : Nat.Prime 1007208101 := by
  apply lucas_primality 1007208101 (2 : ZMod 1007208101)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (10072081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (10072081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007208101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_10072081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1007208101) ^ 503604050 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007208101) ^ 201441620 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007208101) ^ 100 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1075232377 : Nat.Prime 1075232377 := by
  apply lucas_primality 1075232377 (5 : ZMod 1075232377)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (479, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (479, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1075232377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_479
      · exact prime_oneHundredSixtyFB_31177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1075232377) ^ 537616188 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1075232377) ^ 358410792 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1075232377) ^ 2244744 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1075232377) ^ 34488 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_1667
      · exact prime_oneHundredSixtyFB_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1403802133 : Nat.Prime 1403802133 := by
  apply lucas_primality 1403802133 (2 : ZMod 1403802133)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (6881383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (6881383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403802133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_6881383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1403802133) ^ 701901066 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403802133) ^ 467934044 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403802133) ^ 82576596 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403802133) ^ 204 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1639788413 : Nat.Prime 1639788413 := by
  apply lucas_primality 1639788413 (3 : ZMod 1639788413)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (266719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (266719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1639788413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_53
      · exact prime_oneHundredSixtyFB_266719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1639788413) ^ 819894206 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1639788413) ^ 56544428 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1639788413) ^ 30939404 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1639788413) ^ 6148 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1742444437 : Nat.Prime 1742444437 := by
  apply lucas_primality 1742444437 (2 : ZMod 1742444437)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (145203703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (145203703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1742444437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_145203703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1742444437) ^ 871222218 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1742444437) ^ 580814812 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1742444437) ^ 12 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1782268003 : Nat.Prime 1782268003 := by
  apply lucas_primality 1782268003 (2 : ZMod 1782268003)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (33004963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (33004963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1782268003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_33004963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1782268003) ^ 891134001 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782268003) ^ 594089334 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782268003) ^ 54 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1897184077 : Nat.Prime 1897184077 := by
  apply lucas_primality 1897184077 (2 : ZMod 1897184077)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4969, 1), (31817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4969, 1), (31817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1897184077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_4969
      · exact prime_oneHundredSixtyFB_31817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1897184077) ^ 948592038 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1897184077) ^ 632394692 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1897184077) ^ 381804 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1897184077) ^ 59628 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1953042799 : Nat.Prime 1953042799 := by
  apply lucas_primality 1953042799 (3 : ZMod 1953042799)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1953042799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_46501019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1953042799) ^ 976521399 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 651014266 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 279006114 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 42 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2213346269 : Nat.Prime 2213346269 := by
  apply lucas_primality 2213346269 (2 : ZMod 2213346269)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2213346269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11292583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2213346269) ^ 1106673134 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 316192324 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 196 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2376707197 : Nat.Prime 2376707197 := by
  apply lucas_primality 2376707197 (2 : ZMod 2376707197)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (397, 1), (9413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (397, 1), (9413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2376707197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_53
      · exact prime_oneHundredSixtyFB_397
      · exact prime_oneHundredSixtyFB_9413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2376707197) ^ 1188353598 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2376707197) ^ 792235732 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2376707197) ^ 44843532 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2376707197) ^ 5986668 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2376707197) ^ 252492 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_47
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2664705773 : Nat.Prime 2664705773 := by
  apply lucas_primality 2664705773 (2 : ZMod 2664705773)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (431, 1), (1545653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (431, 1), (1545653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2664705773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_431
      · exact prime_oneHundredSixtyFB_1545653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2664705773) ^ 1332352886 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2664705773) ^ 6182612 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2664705773) ^ 1724 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2723851201 : Nat.Prime 2723851201 := by
  apply lucas_primality 2723851201 (29 : ZMod 2723851201)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (37, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (37, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 2723851201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 2723851201) ^ 1361925600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (29 : ZMod 2723851201) ^ 907950400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (29 : ZMod 2723851201) ^ 544770240 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (29 : ZMod 2723851201) ^ 389121600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (29 : ZMod 2723851201) ^ 73617600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (29 : ZMod 2723851201) ^ 8702400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2977549837 : Nat.Prime 2977549837 := by
  apply lucas_primality 2977549837 (2 : ZMod 2977549837)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2977549837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_248129153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2977549837) ^ 1488774918 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 992516612 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 12 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3140442119 : Nat.Prime 3140442119 := by
  apply lucas_primality 3140442119 (11 : ZMod 3140442119)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (3858037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (3858037, 1)] : List FactorBlock).map factorBlockValue).prod) = 3140442119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_3858037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3140442119) ^ 1570221059 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140442119) ^ 285494738 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140442119) ^ 84876814 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140442119) ^ 814 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3188827619 : Nat.Prime 3188827619 := by
  apply lucas_primality 3188827619 (2 : ZMod 3188827619)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (353, 1), (32969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (353, 1), (32969, 1)] : List FactorBlock).map factorBlockValue).prod) = 3188827619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_137
      · exact prime_oneHundredSixtyFB_353
      · exact prime_oneHundredSixtyFB_32969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3188827619) ^ 1594413809 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3188827619) ^ 23276114 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3188827619) ^ 9033506 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3188827619) ^ 96722 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3783224567 : Nat.Prime 3783224567 := by
  apply lucas_primality 3783224567 (5 : ZMod 3783224567)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (7867, 1), (21859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (7867, 1), (21859, 1)] : List FactorBlock).map factorBlockValue).prod) = 3783224567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_7867
      · exact prime_oneHundredSixtyFB_21859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3783224567) ^ 1891612283 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3783224567) ^ 343929506 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3783224567) ^ 480898 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3783224567) ^ 173074 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_4737989713 : Nat.Prime 4737989713 := by
  apply lucas_primality 4737989713 (5 : ZMod 4737989713)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (277, 1), (9631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (277, 1), (9631, 1)] : List FactorBlock).map factorBlockValue).prod) = 4737989713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_277
      · exact prime_oneHundredSixtyFB_9631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4737989713) ^ 2368994856 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737989713) ^ 1579329904 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737989713) ^ 128053776 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737989713) ^ 17104656 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737989713) ^ 491952 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_4853859953 : Nat.Prime 4853859953 := by
  apply lucas_primality 4853859953 (3 : ZMod 4853859953)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4853859953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_47
      · exact prime_oneHundredSixtyFB_150107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4853859953) ^ 2426929976 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 112880464 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 103273616 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 32336 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_31
      · exact prime_oneHundredSixtyFB_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_6219887351 : Nat.Prime 6219887351 := by
  apply lucas_primality 6219887351 (26 : ZMod 6219887351)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (97, 1), (1282451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (97, 1), (1282451, 1)] : List FactorBlock).map factorBlockValue).prod) = 6219887351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_97
      · exact prime_oneHundredSixtyFB_1282451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 6219887351) ^ 3109943675 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (26 : ZMod 6219887351) ^ 1243977470 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (26 : ZMod 6219887351) ^ 64122550 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (26 : ZMod 6219887351) ^ 4850 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_6414582947 : Nat.Prime 6414582947 := by
  apply lucas_primality 6414582947 (2 : ZMod 6414582947)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (719, 1), (4460767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (719, 1), (4460767, 1)] : List FactorBlock).map factorBlockValue).prod) = 6414582947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_719
      · exact prime_oneHundredSixtyFB_4460767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6414582947) ^ 3207291473 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6414582947) ^ 8921534 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6414582947) ^ 1438 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_6612265111 : Nat.Prime 6612265111 := by
  apply lucas_primality 6612265111 (6 : ZMod 6612265111)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (339613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (339613, 1)] : List FactorBlock).map factorBlockValue).prod) = 6612265111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_59
      · exact prime_oneHundredSixtyFB_339613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6612265111) ^ 3306132555 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6612265111) ^ 2204088370 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6612265111) ^ 1322453022 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6612265111) ^ 601115010 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6612265111) ^ 112072290 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6612265111) ^ 19470 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_8375822333 : Nat.Prime 8375822333 := by
  apply lucas_primality 8375822333 (2 : ZMod 8375822333)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (461, 1), (4542203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (461, 1), (4542203, 1)] : List FactorBlock).map factorBlockValue).prod) = 8375822333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_461
      · exact prime_oneHundredSixtyFB_4542203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8375822333) ^ 4187911166 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8375822333) ^ 18168812 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8375822333) ^ 1844 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_9213668617 : Nat.Prime 9213668617 := by
  apply lucas_primality 9213668617 (7 : ZMod 9213668617)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6857, 1), (55987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6857, 1), (55987, 1)] : List FactorBlock).map factorBlockValue).prod) = 9213668617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_6857
      · exact prime_oneHundredSixtyFB_55987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9213668617) ^ 4606834308 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 9213668617) ^ 3071222872 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 9213668617) ^ 1343688 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 9213668617) ^ 164568 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_9462166499 : Nat.Prime 9462166499 := by
  apply lucas_primality 9462166499 (2 : ZMod 9462166499)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (57001003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (57001003, 1)] : List FactorBlock).map factorBlockValue).prod) = 9462166499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_83
      · exact prime_oneHundredSixtyFB_57001003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9462166499) ^ 4731083249 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9462166499) ^ 114002006 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9462166499) ^ 166 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_10179828163 : Nat.Prime 10179828163 := by
  apply lucas_primality 10179828163 (3 : ZMod 10179828163)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (5233, 1), (15439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (5233, 1), (15439, 1)] : List FactorBlock).map factorBlockValue).prod) = 10179828163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_5233
      · exact prime_oneHundredSixtyFB_15439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10179828163) ^ 5089914081 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10179828163) ^ 3393276054 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10179828163) ^ 1454261166 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10179828163) ^ 1945314 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10179828163) ^ 659358 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_10717481219 : Nat.Prime 10717481219 := by
  apply lucas_primality 10717481219 (2 : ZMod 10717481219)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32999, 1), (162391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32999, 1), (162391, 1)] : List FactorBlock).map factorBlockValue).prod) = 10717481219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_32999
      · exact prime_oneHundredSixtyFB_162391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10717481219) ^ 5358740609 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10717481219) ^ 324782 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10717481219) ^ 65998 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_20888581501 : Nat.Prime 20888581501 := by
  apply lucas_primality 20888581501 (6 : ZMod 20888581501)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 3), (4641907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 3), (4641907, 1)] : List FactorBlock).map factorBlockValue).prod) = 20888581501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_4641907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 20888581501) ^ 10444290750 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 20888581501) ^ 6962860500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 20888581501) ^ 4177716300 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 20888581501) ^ 4500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_79
      · exact prime_oneHundredSixtyFB_163
      · exact prime_oneHundredSixtyFB_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_25123536953 : Nat.Prime 25123536953 := by
  apply lucas_primality 25123536953 (3 : ZMod 25123536953)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3140442119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3140442119, 1)] : List FactorBlock).map factorBlockValue).prod) = 25123536953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3140442119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 25123536953) ^ 12561768476 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 25123536953) ^ 8 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_26451306313 : Nat.Prime 26451306313 := by
  apply lucas_primality 26451306313 (10 : ZMod 26451306313)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1009, 1), (1092307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1009, 1), (1092307, 1)] : List FactorBlock).map factorBlockValue).prod) = 26451306313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_1009
      · exact prime_oneHundredSixtyFB_1092307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 26451306313) ^ 13225653156 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (10 : ZMod 26451306313) ^ 8817102104 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (10 : ZMod 26451306313) ^ 26215368 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (10 : ZMod 26451306313) ^ 24216 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_27238512011 : Nat.Prime 27238512011 := by
  apply lucas_primality 27238512011 (2 : ZMod 27238512011)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2723851201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2723851201, 1)] : List FactorBlock).map factorBlockValue).prod) = 27238512011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_2723851201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27238512011) ^ 13619256005 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27238512011) ^ 5447702402 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27238512011) ^ 10 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_28666928111 : Nat.Prime 28666928111 := by
  apply lucas_primality 28666928111 (19 : ZMod 28666928111)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (769, 1), (196201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (769, 1), (196201, 1)] : List FactorBlock).map factorBlockValue).prod) = 28666928111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_769
      · exact prime_oneHundredSixtyFB_196201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 28666928111) ^ 14333464055 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 28666928111) ^ 5733385622 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 28666928111) ^ 1508785690 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 28666928111) ^ 37278190 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 28666928111) ^ 146110 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_41522732507 : Nat.Prime 41522732507 := by
  apply lucas_primality 41522732507 (2 : ZMod 41522732507)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (43, 1), (25411709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (43, 1), (25411709, 1)] : List FactorBlock).map factorBlockValue).prod) = 41522732507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_25411709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41522732507) ^ 20761366253 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 41522732507) ^ 2185406974 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 41522732507) ^ 965644942 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 41522732507) ^ 1634 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_50254933999 : Nat.Prime 50254933999 := by
  apply lucas_primality 50254933999 (3 : ZMod 50254933999)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8375822333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8375822333, 1)] : List FactorBlock).map factorBlockValue).prod) = 50254933999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_8375822333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50254933999) ^ 25127466999 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 50254933999) ^ 16751644666 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 50254933999) ^ 6 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_61538065751 : Nat.Prime 61538065751 := by
  apply lucas_primality 61538065751 (13 : ZMod 61538065751)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (61, 1), (576469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (61, 1), (576469, 1)] : List FactorBlock).map factorBlockValue).prod) = 61538065751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_61
      · exact prime_oneHundredSixtyFB_576469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 61538065751) ^ 30769032875 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 61538065751) ^ 12307613150 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 61538065751) ^ 8791152250 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 61538065751) ^ 1008820750 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 61538065751) ^ 106750 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_62113629811 : Nat.Prime 62113629811 := by
  apply lucas_primality 62113629811 (2 : ZMod 62113629811)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (121791431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (121791431, 1)] : List FactorBlock).map factorBlockValue).prod) = 62113629811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_121791431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62113629811) ^ 31056814905 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 62113629811) ^ 20704543270 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 62113629811) ^ 12422725962 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 62113629811) ^ 3653742930 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 62113629811) ^ 510 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_100059262279 : Nat.Prime 100059262279 := by
  apply lucas_primality 100059262279 (3 : ZMod 100059262279)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (47, 1), (602411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (47, 1), (602411, 1)] : List FactorBlock).map factorBlockValue).prod) = 100059262279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_31
      · exact prime_oneHundredSixtyFB_47
      · exact prime_oneHundredSixtyFB_602411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100059262279) ^ 50029631139 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 33353087426 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 5266276962 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 3227718138 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 2128920474 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 166098 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_100803344111 : Nat.Prime 100803344111 := by
  apply lucas_primality 100803344111 (7 : ZMod 100803344111)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (71, 1), (709, 1), (28607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (71, 1), (709, 1), (28607, 1)] : List FactorBlock).map factorBlockValue).prod) = 100803344111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_709
      · exact prime_oneHundredSixtyFB_28607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 100803344111) ^ 50401672055 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 100803344111) ^ 20160668822 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 100803344111) ^ 14400477730 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 100803344111) ^ 1419765410 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 100803344111) ^ 142176790 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 100803344111) ^ 3523730 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_103382998727 : Nat.Prime 103382998727 := by
  apply lucas_primality 103382998727 (5 : ZMod 103382998727)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (3109, 1), (32537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (3109, 1), (32537, 1)] : List FactorBlock).map factorBlockValue).prod) = 103382998727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_73
      · exact prime_oneHundredSixtyFB_3109
      · exact prime_oneHundredSixtyFB_32537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 103382998727) ^ 51691499363 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 103382998727) ^ 14768999818 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 103382998727) ^ 1416205462 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 103382998727) ^ 33252814 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 103382998727) ^ 3177398 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_853
      · exact prime_oneHundredSixtyFB_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_153088976401 : Nat.Prime 153088976401 := by
  apply lucas_primality 153088976401 (19 : ZMod 153088976401)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (3221, 1), (39607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (3221, 1), (39607, 1)] : List FactorBlock).map factorBlockValue).prod) = 153088976401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_3221
      · exact prime_oneHundredSixtyFB_39607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 153088976401) ^ 76544488200 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 51029658800 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 30617795280 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 47528400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 3865200 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_172177267453 : Nat.Prime 172177267453 := by
  apply lucas_primality 172177267453 (5 : ZMod 172177267453)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (17957579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (17957579, 1)] : List FactorBlock).map factorBlockValue).prod) = 172177267453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_47
      · exact prime_oneHundredSixtyFB_17957579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 172177267453) ^ 86088633726 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 57392422484 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 10128074556 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 3663346116 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 9588 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_174274016963 : Nat.Prime 174274016963 := by
  apply lucas_primality 174274016963 (2 : ZMod 174274016963)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73387, 1), (1187363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73387, 1), (1187363, 1)] : List FactorBlock).map factorBlockValue).prod) = 174274016963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_73387
      · exact prime_oneHundredSixtyFB_1187363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 174274016963) ^ 87137008481 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 174274016963) ^ 2374726 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 174274016963) ^ 146774 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_215565659143 : Nat.Prime 215565659143 := by
  apply lucas_primality 215565659143 (3 : ZMod 215565659143)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) = 215565659143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_47
      · exact prime_oneHundredSixtyFB_764417231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 215565659143) ^ 107782829571 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 71855219714 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 4586503386 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 282 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_227665528093 : Nat.Prime 227665528093 := by
  apply lucas_primality 227665528093 (5 : ZMod 227665528093)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (61, 1), (503, 1), (22901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (61, 1), (503, 1), (22901, 1)] : List FactorBlock).map factorBlockValue).prod) = 227665528093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_61
      · exact prime_oneHundredSixtyFB_503
      · exact prime_oneHundredSixtyFB_22901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 227665528093) ^ 113832764046 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 227665528093) ^ 75888509364 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 227665528093) ^ 3732221772 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 227665528093) ^ 452615364 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 227665528093) ^ 9941292 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_276099113611 : Nat.Prime 276099113611 := by
  apply lucas_primality 276099113611 (2 : ZMod 276099113611)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (29, 1), (71, 1), (87643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (29, 1), (71, 1), (87643, 1)] : List FactorBlock).map factorBlockValue).prod) = 276099113611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_87643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 276099113611) ^ 138049556805 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 92033037870 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 55219822722 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 16241124330 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 9520659090 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 3888719910 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 3150270 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_324699246947 : Nat.Prime 324699246947 := by
  apply lucas_primality 324699246947 (2 : ZMod 324699246947)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) = 324699246947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_659
      · exact prime_oneHundredSixtyFB_1289
      · exact prime_oneHundredSixtyFB_191123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 324699246947) ^ 162349623473 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 492715094 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 251900114 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 1698902 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_344003137333 : Nat.Prime 344003137333 := by
  apply lucas_primality 344003137333 (6 : ZMod 344003137333)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (28666928111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (28666928111, 1)] : List FactorBlock).map factorBlockValue).prod) = 344003137333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_28666928111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 344003137333) ^ 172001568666 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 344003137333) ^ 114667712444 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 344003137333) ^ 12 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_402050464063 : Nat.Prime 402050464063 := by
  apply lucas_primality 402050464063 (17 : ZMod 402050464063)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (179, 1), (2671, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (179, 1), (2671, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) = 402050464063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_179
      · exact prime_oneHundredSixtyFB_2671
      · exact prime_oneHundredSixtyFB_10781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 402050464063) ^ 201025232031 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 402050464063) ^ 134016821354 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 402050464063) ^ 30926958774 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 402050464063) ^ 2246091978 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 402050464063) ^ 150524322 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 402050464063) ^ 37292502 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_446011079209 : Nat.Prime 446011079209 := by
  apply lucas_primality 446011079209 (7 : ZMod 446011079209)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) = 446011079209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_31
      · exact prime_oneHundredSixtyFB_829
      · exact prime_oneHundredSixtyFB_723133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 446011079209) ^ 223005539604 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 148670359736 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 14387454168 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 538010952 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 616776 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_541003830541 : Nat.Prime 541003830541 := by
  apply lucas_primality 541003830541 (7 : ZMod 541003830541)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (10613, 1), (849593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (10613, 1), (849593, 1)] : List FactorBlock).map factorBlockValue).prod) = 541003830541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_10613
      · exact prime_oneHundredSixtyFB_849593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 541003830541) ^ 270501915270 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 541003830541) ^ 180334610180 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 541003830541) ^ 108200766108 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 541003830541) ^ 50975580 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 541003830541) ^ 636780 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_556631816341 : Nat.Prime 556631816341 := by
  apply lucas_primality 556631816341 (11 : ZMod 556631816341)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (545717467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (545717467, 1)] : List FactorBlock).map factorBlockValue).prod) = 556631816341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_545717467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 556631816341) ^ 278315908170 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 556631816341) ^ 185543938780 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 556631816341) ^ 111326363268 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 556631816341) ^ 32743048020 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 556631816341) ^ 1020 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_558341716703 : Nat.Prime 558341716703 := by
  apply lucas_primality 558341716703 (5 : ZMod 558341716703)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (54449, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (54449, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) = 558341716703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_54449
      · exact prime_oneHundredSixtyFB_66587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 558341716703) ^ 279170858351 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 558341716703) ^ 79763102386 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 558341716703) ^ 50758337882 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 558341716703) ^ 10254398 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 558341716703) ^ 8385146 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_724221389597 : Nat.Prime 724221389597 := by
  apply lucas_primality 724221389597 (2 : ZMod 724221389597)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (409, 1), (442678111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (409, 1), (442678111, 1)] : List FactorBlock).map factorBlockValue).prod) = 724221389597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_409
      · exact prime_oneHundredSixtyFB_442678111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 724221389597) ^ 362110694798 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 724221389597) ^ 1770712444 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 724221389597) ^ 1636 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_746015578621 : Nat.Prime 746015578621 := by
  apply lucas_primality 746015578621 (2 : ZMod 746015578621)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (23, 1), (251, 1), (165673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (23, 1), (251, 1), (165673, 1)] : List FactorBlock).map factorBlockValue).prod) = 746015578621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_251
      · exact prime_oneHundredSixtyFB_165673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 746015578621) ^ 373007789310 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746015578621) ^ 248671859540 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746015578621) ^ 149203115724 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746015578621) ^ 57385813740 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746015578621) ^ 32435459940 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746015578621) ^ 2972173620 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746015578621) ^ 4502940 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_779284339133 : Nat.Prime 779284339133 := by
  apply lucas_primality 779284339133 (2 : ZMod 779284339133)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (521, 1), (3461, 1), (8311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (521, 1), (3461, 1), (8311, 1)] : List FactorBlock).map factorBlockValue).prod) = 779284339133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_521
      · exact prime_oneHundredSixtyFB_3461
      · exact prime_oneHundredSixtyFB_8311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 779284339133) ^ 389642169566 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 779284339133) ^ 59944949164 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 779284339133) ^ 1495747292 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 779284339133) ^ 225161612 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 779284339133) ^ 93765412 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_847909006459 : Nat.Prime 847909006459 := by
  apply lucas_primality 847909006459 (3 : ZMod 847909006459)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (37, 1), (131703791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (37, 1), (131703791, 1)] : List FactorBlock).map factorBlockValue).prod) = 847909006459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_131703791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 847909006459) ^ 423954503229 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 847909006459) ^ 282636335486 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 847909006459) ^ 29238241602 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 847909006459) ^ 22916459634 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 847909006459) ^ 6438 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_869608720249 : Nat.Prime 869608720249 := by
  apply lucas_primality 869608720249 (14 : ZMod 869608720249)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (809, 1), (44788253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (809, 1), (44788253, 1)] : List FactorBlock).map factorBlockValue).prod) = 869608720249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_809
      · exact prime_oneHundredSixtyFB_44788253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 869608720249) ^ 434804360124 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 869608720249) ^ 289869573416 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 869608720249) ^ 1074918072 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 869608720249) ^ 19416 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_955633666051 : Nat.Prime 955633666051 := by
  apply lucas_primality 955633666051 (7 : ZMod 955633666051)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (303375767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (303375767, 1)] : List FactorBlock).map factorBlockValue).prod) = 955633666051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_303375767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 955633666051) ^ 477816833025 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 955633666051) ^ 318544555350 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 955633666051) ^ 191126733210 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 955633666051) ^ 136519095150 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 955633666051) ^ 3150 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1181699726089 : Nat.Prime 1181699726089 := by
  apply lucas_primality 1181699726089 (31 : ZMod 1181699726089)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (101, 1), (167, 1), (417023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (101, 1), (167, 1), (417023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1181699726089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_101
      · exact prime_oneHundredSixtyFB_167
      · exact prime_oneHundredSixtyFB_417023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1181699726089) ^ 590849863044 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 393899908696 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 168814246584 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 11699997288 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 7076046264 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 2833656 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1483998585427 : Nat.Prime 1483998585427 := by
  apply lucas_primality 1483998585427 (3 : ZMod 1483998585427)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (42863, 1), (274777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (42863, 1), (274777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483998585427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_42863
      · exact prime_oneHundredSixtyFB_274777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1483998585427) ^ 741999292713 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 494666195142 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 211999797918 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 34621902 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 5400738 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2503522305341 : Nat.Prime 2503522305341 := by
  apply lucas_primality 2503522305341 (2 : ZMod 2503522305341)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (71, 1), (2309, 1), (5741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (71, 1), (2309, 1), (5741, 1)] : List FactorBlock).map factorBlockValue).prod) = 2503522305341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_2309
      · exact prime_oneHundredSixtyFB_5741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2503522305341) ^ 1251761152670 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2503522305341) ^ 500704461068 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2503522305341) ^ 357646043620 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2503522305341) ^ 131764331860 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2503522305341) ^ 35260877540 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2503522305341) ^ 1084245260 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2503522305341) ^ 436077740 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2666852251417 : Nat.Prime 2666852251417 := by
  apply lucas_primality 2666852251417 (5 : ZMod 2666852251417)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (17, 1), (726266953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (17, 1), (726266953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2666852251417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_726266953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2666852251417) ^ 1333426125708 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2666852251417) ^ 888950750472 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2666852251417) ^ 156873661848 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2666852251417) ^ 3672 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2724679354157 : Nat.Prime 2724679354157 := by
  apply lucas_primality 2724679354157 (2 : ZMod 2724679354157)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (33589, 1), (56489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (33589, 1), (56489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2724679354157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_359
      · exact prime_oneHundredSixtyFB_33589
      · exact prime_oneHundredSixtyFB_56489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2724679354157) ^ 1362339677078 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2724679354157) ^ 7589636084 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2724679354157) ^ 81118204 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2724679354157) ^ 48233804 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2826449402141 : Nat.Prime 2826449402141 := by
  apply lucas_primality 2826449402141 (2 : ZMod 2826449402141)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (13, 1), (109, 1), (2035379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (13, 1), (109, 1), (2035379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2826449402141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_109
      · exact prime_oneHundredSixtyFB_2035379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2826449402141) ^ 1413224701070 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826449402141) ^ 565289880428 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826449402141) ^ 403778486020 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826449402141) ^ 217419184780 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826449402141) ^ 25930728460 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826449402141) ^ 1388660 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_5652898804283 : Nat.Prime 5652898804283 := by
  apply lucas_primality 5652898804283 (2 : ZMod 5652898804283)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2826449402141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2826449402141, 1)] : List FactorBlock).map factorBlockValue).prod) = 5652898804283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_2826449402141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5652898804283) ^ 2826449402141 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5652898804283) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_5848995038801 : Nat.Prime 5848995038801 := by
  apply lucas_primality 5848995038801 (3 : ZMod 5848995038801)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (103, 1), (141965899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (103, 1), (141965899, 1)] : List FactorBlock).map factorBlockValue).prod) = 5848995038801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_103
      · exact prime_oneHundredSixtyFB_141965899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5848995038801) ^ 2924497519400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5848995038801) ^ 1169799007760 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5848995038801) ^ 56786359600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5848995038801) ^ 41200 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_6700100600437 : Nat.Prime 6700100600437 := by
  apply lucas_primality 6700100600437 (2 : ZMod 6700100600437)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (558341716703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (558341716703, 1)] : List FactorBlock).map factorBlockValue).prod) = 6700100600437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_558341716703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6700100600437) ^ 3350050300218 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6700100600437) ^ 2233366866812 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6700100600437) ^ 12 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_7565073605519 : Nat.Prime 7565073605519 := by
  apply lucas_primality 7565073605519 (11 : ZMod 7565073605519)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (26451306313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (26451306313, 1)] : List FactorBlock).map factorBlockValue).prod) = 7565073605519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_26451306313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7565073605519) ^ 3782536802759 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 7565073605519) ^ 687733964138 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 7565073605519) ^ 581928738886 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 7565073605519) ^ 286 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_8450556055043 : Nat.Prime 8450556055043 := by
  apply lucas_primality 8450556055043 (2 : ZMod 8450556055043)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) = 8450556055043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_83
      · exact prime_oneHundredSixtyFB_2213346269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8450556055043) ^ 4225278027521 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 367415480654 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 101813928374 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 3818 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_8750286887521 : Nat.Prime 8750286887521 := by
  apply lucas_primality 8750286887521 (19 : ZMod 8750286887521)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (23209, 1), (785461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (23209, 1), (785461, 1)] : List FactorBlock).map factorBlockValue).prod) = 8750286887521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_23209
      · exact prime_oneHundredSixtyFB_785461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 8750286887521) ^ 4375143443760 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 8750286887521) ^ 2916762295840 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 8750286887521) ^ 1750057377504 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 8750286887521) ^ 377021280 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (19 : ZMod 8750286887521) ^ 11140320 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_9566065542823 : Nat.Prime 9566065542823 := by
  apply lucas_primality 9566065542823 (5 : ZMod 9566065542823)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) = 9566065542823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_2347
      · exact prime_oneHundredSixtyFB_679311571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9566065542823) ^ 4783032771411 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 3188688514274 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 4075869426 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 14082 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_229
      · exact prime_oneHundredSixtyFB_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_11046092917481 : Nat.Prime 11046092917481 := by
  apply lucas_primality 11046092917481 (3 : ZMod 11046092917481)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (49481, 1), (5580977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (49481, 1), (5580977, 1)] : List FactorBlock).map factorBlockValue).prod) = 11046092917481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_49481
      · exact prime_oneHundredSixtyFB_5580977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11046092917481) ^ 5523046458740 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11046092917481) ^ 2209218583496 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11046092917481) ^ 223239080 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11046092917481) ^ 1979240 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_14286766865669 : Nat.Prime 14286766865669 := by
  apply lucas_primality 14286766865669 (2 : ZMod 14286766865669)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) = 14286766865669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_324699246947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14286766865669) ^ 7143383432834 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 1298796987788 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 44 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_22507016516591 : Nat.Prime 22507016516591 := by
  apply lucas_primality 22507016516591 (43 : ZMod 22507016516591)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (631, 1), (21882703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (631, 1), (21882703, 1)] : List FactorBlock).map factorBlockValue).prod) = 22507016516591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_163
      · exact prime_oneHundredSixtyFB_631
      · exact prime_oneHundredSixtyFB_21882703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 22507016516591) ^ 11253508258295 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (43 : ZMod 22507016516591) ^ 4501403303318 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (43 : ZMod 22507016516591) ^ 138079855930 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (43 : ZMod 22507016516591) ^ 35668805890 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (43 : ZMod 22507016516591) ^ 1028530 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_30073867051861 : Nat.Prime 30073867051861 := by
  apply lucas_primality 30073867051861 (2 : ZMod 30073867051861)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (43, 1), (6337, 1), (21143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (43, 1), (6337, 1), (21143, 1)] : List FactorBlock).map factorBlockValue).prod) = 30073867051861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_6337
      · exact prime_oneHundredSixtyFB_21143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30073867051861) ^ 15036933525930 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 10024622350620 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 6014773410372 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 1037029898340 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 699392257020 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 4745757780 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 1422403020 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_30184480354109 : Nat.Prime 30184480354109 := by
  apply lucas_primality 30184480354109 (2 : ZMod 30184480354109)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (547, 1), (51827, 1), (266183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (547, 1), (51827, 1), (266183, 1)] : List FactorBlock).map factorBlockValue).prod) = 30184480354109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_547
      · exact prime_oneHundredSixtyFB_51827
      · exact prime_oneHundredSixtyFB_266183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30184480354109) ^ 15092240177054 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30184480354109) ^ 55181865364 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30184480354109) ^ 582408404 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 30184480354109) ^ 113397476 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_32520964175027 : Nat.Prime 32520964175027 := by
  apply lucas_primality 32520964175027 (2 : ZMod 32520964175027)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) = 32520964175027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_53
      · exact prime_oneHundredSixtyFB_1151
      · exact prime_oneHundredSixtyFB_266552171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32520964175027) ^ 16260482087513 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 613603097642 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 28254530126 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 122006 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_38009070719731 : Nat.Prime 38009070719731 := by
  apply lucas_primality 38009070719731 (2 : ZMod 38009070719731)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (367, 1), (34871027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (367, 1), (34871027, 1)] : List FactorBlock).map factorBlockValue).prod) = 38009070719731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_367
      · exact prime_oneHundredSixtyFB_34871027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38009070719731) ^ 19004535359865 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 12669690239910 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 7601814143946 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 3455370065430 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 103566950190 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 1089990 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_96697
      · exact prime_oneHundredSixtyFB_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_61638694796963 : Nat.Prime 61638694796963 := by
  apply lucas_primality 61638694796963 (2 : ZMod 61638694796963)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (43, 1), (349, 1), (3637, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (43, 1), (349, 1), (3637, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) = 61638694796963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_349
      · exact prime_oneHundredSixtyFB_3637
      · exact prime_oneHundredSixtyFB_19471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61638694796963) ^ 30819347398481 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 2125472234378 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 1433458018534 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 176615171338 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 16947675226 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 3165666622 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_173
      · exact prime_oneHundredSixtyFB_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_107098513236541 : Nat.Prime 107098513236541 := by
  apply lucas_primality 107098513236541 (2 : ZMod 107098513236541)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (131441, 1), (646669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (131441, 1), (646669, 1)] : List FactorBlock).map factorBlockValue).prod) = 107098513236541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_131441
      · exact prime_oneHundredSixtyFB_646669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 107098513236541) ^ 53549256618270 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 107098513236541) ^ 35699504412180 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 107098513236541) ^ 21419702647308 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 107098513236541) ^ 15299787605220 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 107098513236541) ^ 814802940 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 107098513236541) ^ 165615660 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_126576327249287 : Nat.Prime 126576327249287 := by
  apply lucas_primality 126576327249287 (5 : ZMod 126576327249287)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33359, 1), (1897184077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33359, 1), (1897184077, 1)] : List FactorBlock).map factorBlockValue).prod) = 126576327249287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_33359
      · exact prime_oneHundredSixtyFB_1897184077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 126576327249287) ^ 63288163624643 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 126576327249287) ^ 3794368154 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 126576327249287) ^ 66718 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_139034446677491 : Nat.Prime 139034446677491 := by
  apply lucas_primality 139034446677491 (2 : ZMod 139034446677491)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) = 139034446677491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_443
      · exact prime_oneHundredSixtyFB_18151967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139034446677491) ^ 69517223338745 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 27806889335498 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 19862063811070 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 10694957436730 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7317602456710 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 313847509430 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7659470 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_150070644909607 : Nat.Prime 150070644909607 := by
  apply lucas_primality 150070644909607 (3 : ZMod 150070644909607)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (619, 1), (1087, 1), (37172717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (619, 1), (1087, 1), (37172717, 1)] : List FactorBlock).map factorBlockValue).prod) = 150070644909607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_619
      · exact prime_oneHundredSixtyFB_1087
      · exact prime_oneHundredSixtyFB_37172717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150070644909607) ^ 75035322454803 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 150070644909607) ^ 50023548303202 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 150070644909607) ^ 242440460274 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 150070644909607) ^ 138059470938 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 150070644909607) ^ 4037118 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_158450763619817 : Nat.Prime 158450763619817 := by
  apply lucas_primality 158450763619817 (3 : ZMod 158450763619817)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (111827, 1), (177115951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (111827, 1), (177115951, 1)] : List FactorBlock).map factorBlockValue).prod) = 158450763619817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_111827
      · exact prime_oneHundredSixtyFB_177115951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 158450763619817) ^ 79225381809908 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 158450763619817) ^ 1416927608 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 158450763619817) ^ 894616 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_197320078064177 : Nat.Prime 197320078064177 := by
  apply lucas_primality 197320078064177 (3 : ZMod 197320078064177)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) = 197320078064177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_1327
      · exact prime_oneHundredSixtyFB_4273
      · exact prime_oneHundredSixtyFB_2174941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197320078064177) ^ 98660039032088 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 148696366288 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 46178347312 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 90724336 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_10789
      · exact prime_oneHundredSixtyFB_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_334989034308223 : Nat.Prime 334989034308223 := by
  apply lucas_primality 334989034308223 (3 : ZMod 334989034308223)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) = 334989034308223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_37
      · exact prime_oneHundredSixtyFB_215565659143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 334989034308223) ^ 167494517154111 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 111663011436074 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 47855576329746 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 9053757684006 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 1554 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_383611913911283 : Nat.Prime 383611913911283 := by
  apply lucas_primality 383611913911283 (2 : ZMod 383611913911283)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (787, 1), (9739, 1), (72959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (787, 1), (9739, 1), (72959, 1)] : List FactorBlock).map factorBlockValue).prod) = 383611913911283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_787
      · exact prime_oneHundredSixtyFB_9739
      · exact prime_oneHundredSixtyFB_72959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 383611913911283) ^ 191805956955641 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 54801701987326 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 487435722886 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 39389250838 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 5257910798 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_386934201013153 : Nat.Prime 386934201013153 := by
  apply lucas_primality 386934201013153 (7 : ZMod 386934201013153)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (390389, 1), (794191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (390389, 1), (794191, 1)] : List FactorBlock).map factorBlockValue).prod) = 386934201013153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_390389
      · exact prime_oneHundredSixtyFB_794191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 386934201013153) ^ 193467100506576 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 386934201013153) ^ 128978067004384 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 386934201013153) ^ 29764169308704 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 386934201013153) ^ 991150368 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 386934201013153) ^ 487205472 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_416923693962317 : Nat.Prime 416923693962317 := by
  apply lucas_primality 416923693962317 (2 : ZMod 416923693962317)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1445117, 1), (72126287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1445117, 1), (72126287, 1)] : List FactorBlock).map factorBlockValue).prod) = 416923693962317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_1445117
      · exact prime_oneHundredSixtyFB_72126287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 416923693962317) ^ 208461846981158 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 416923693962317) ^ 288505148 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 416923693962317) ^ 5780468 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_466718517702823 : Nat.Prime 466718517702823 := by
  apply lucas_primality 466718517702823 (3 : ZMod 466718517702823)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (23057, 1), (43813733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (23057, 1), (43813733, 1)] : List FactorBlock).map factorBlockValue).prod) = 466718517702823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_23057
      · exact prime_oneHundredSixtyFB_43813733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 466718517702823) ^ 233359258851411 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 155572839234274 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 66674073957546 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 42428956154802 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 20241944646 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 10652334 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_734546280944473 : Nat.Prime 734546280944473 := by
  apply lucas_primality 734546280944473 (5 : ZMod 734546280944473)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (111637, 1), (274157269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (111637, 1), (274157269, 1)] : List FactorBlock).map factorBlockValue).prod) = 734546280944473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_111637
      · exact prime_oneHundredSixtyFB_274157269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 734546280944473) ^ 367273140472236 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 734546280944473) ^ 244848760314824 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 734546280944473) ^ 6579774456 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 734546280944473) ^ 2679288 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_767223827822567 : Nat.Prime 767223827822567 := by
  apply lucas_primality 767223827822567 (5 : ZMod 767223827822567)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383611913911283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383611913911283, 1)] : List FactorBlock).map factorBlockValue).prod) = 767223827822567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_383611913911283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 767223827822567) ^ 383611913911283 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 767223827822567) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_972840324054971 : Nat.Prime 972840324054971 := by
  apply lucas_primality 972840324054971 (6 : ZMod 972840324054971)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (569, 1), (1009, 1), (3947, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (569, 1), (1009, 1), (3947, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) = 972840324054971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_569
      · exact prime_oneHundredSixtyFB_1009
      · exact prime_oneHundredSixtyFB_3947
      · exact prime_oneHundredSixtyFB_6133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 972840324054971) ^ 486420162027485 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 194568064810994 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 138977189150710 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 1709736949130 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 964162858330 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 246475886510 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 158623891090 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1295182208051857 : Nat.Prime 1295182208051857 := by
  apply lucas_primality 1295182208051857 (7 : ZMod 1295182208051857)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (29, 1), (103382998727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (29, 1), (103382998727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295182208051857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_103382998727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1295182208051857) ^ 647591104025928 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295182208051857) ^ 431727402683952 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295182208051857) ^ 44661455450064 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295182208051857) ^ 12528 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1427292785177339 : Nat.Prime 1427292785177339 := by
  apply lucas_primality 1427292785177339 (2 : ZMod 1427292785177339)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (139, 1), (66067, 1), (2679697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (139, 1), (66067, 1), (2679697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427292785177339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_139
      · exact prime_oneHundredSixtyFB_66067
      · exact prime_oneHundredSixtyFB_2679697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1427292785177339) ^ 713646392588669 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427292785177339) ^ 49216992592322 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427292785177339) ^ 10268293418542 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427292785177339) ^ 21603717214 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427292785177339) ^ 532632154 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1485937637257769 : Nat.Prime 1485937637257769 := by
  apply lucas_primality 1485937637257769 (3 : ZMod 1485937637257769)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6318211, 1), (29397911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6318211, 1), (29397911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1485937637257769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_6318211
      · exact prime_oneHundredSixtyFB_29397911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1485937637257769) ^ 742968818628884 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1485937637257769) ^ 235183288 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1485937637257769) ^ 50545688 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1769293600347029 : Nat.Prime 1769293600347029 := by
  apply lucas_primality 1769293600347029 (2 : ZMod 1769293600347029)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (367, 1), (172177267453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (367, 1), (172177267453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769293600347029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_367
      · exact prime_oneHundredSixtyFB_172177267453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1769293600347029) ^ 884646800173514 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769293600347029) ^ 252756228621004 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769293600347029) ^ 4820963488684 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769293600347029) ^ 10276 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2798467569041411 : Nat.Prime 2798467569041411 := by
  apply lucas_primality 2798467569041411 (2 : ZMod 2798467569041411)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (4339, 1), (9213668617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (4339, 1), (9213668617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2798467569041411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_4339
      · exact prime_oneHundredSixtyFB_9213668617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2798467569041411) ^ 1399233784520705 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2798467569041411) ^ 559693513808282 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2798467569041411) ^ 399781081291630 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2798467569041411) ^ 644956803190 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2798467569041411) ^ 303730 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2903136834171983 : Nat.Prime 2903136834171983 := by
  apply lucas_primality 2903136834171983 (5 : ZMod 2903136834171983)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (69491, 1), (20888581501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (69491, 1), (20888581501, 1)] : List FactorBlock).map factorBlockValue).prod) = 2903136834171983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_69491
      · exact prime_oneHundredSixtyFB_20888581501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2903136834171983) ^ 1451568417085991 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2903136834171983) ^ 41777163002 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2903136834171983) ^ 138982 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3377759102642053 : Nat.Prime 3377759102642053 := by
  apply lucas_primality 3377759102642053 (2 : ZMod 3377759102642053)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (569, 1), (8009, 1), (20589017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (569, 1), (8009, 1), (20589017, 1)] : List FactorBlock).map factorBlockValue).prod) = 3377759102642053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_569
      · exact prime_oneHundredSixtyFB_8009
      · exact prime_oneHundredSixtyFB_20589017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3377759102642053) ^ 1688879551321026 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3377759102642053) ^ 1125919700880684 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3377759102642053) ^ 5936307737508 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3377759102642053) ^ 421745424228 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3377759102642053) ^ 164056356 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_5723431519180313 : Nat.Prime 5723431519180313 := by
  apply lucas_primality 5723431519180313 (3 : ZMod 5723431519180313)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (137, 1), (746015578621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (137, 1), (746015578621, 1)] : List FactorBlock).map factorBlockValue).prod) = 5723431519180313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_137
      · exact prime_oneHundredSixtyFB_746015578621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5723431519180313) ^ 2861715759590156 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5723431519180313) ^ 817633074168616 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5723431519180313) ^ 41776872402776 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5723431519180313) ^ 7672 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_5808790066327169 : Nat.Prime 5808790066327169 := by
  apply lucas_primality 5808790066327169 (3 : ZMod 5808790066327169)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (43, 1), (73, 1), (293, 1), (1277, 1), (38639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (43, 1), (73, 1), (293, 1), (1277, 1), (38639, 1)] : List FactorBlock).map factorBlockValue).prod) = 5808790066327169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_73
      · exact prime_oneHundredSixtyFB_293
      · exact prime_oneHundredSixtyFB_1277
      · exact prime_oneHundredSixtyFB_38639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5808790066327169) ^ 2904395033163584 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 135088141077376 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 79572466662016 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 19825222069376 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 4548778438784 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 150334896512 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_10557663666757063 : Nat.Prime 10557663666757063 := by
  apply lucas_primality 10557663666757063 (3 : ZMod 10557663666757063)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (537583, 1), (142312553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (537583, 1), (142312553, 1)] : List FactorBlock).map factorBlockValue).prod) = 10557663666757063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_537583
      · exact prime_oneHundredSixtyFB_142312553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10557663666757063) ^ 5278831833378531 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10557663666757063) ^ 3519221222252354 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10557663666757063) ^ 459028855076394 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10557663666757063) ^ 19639132314 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10557663666757063) ^ 74186454 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_11154318519030139 : Nat.Prime 11154318519030139 := by
  apply lucas_primality 11154318519030139 (2 : ZMod 11154318519030139)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (16432069, 1), (37711889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (16432069, 1), (37711889, 1)] : List FactorBlock).map factorBlockValue).prod) = 11154318519030139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_16432069
      · exact prime_oneHundredSixtyFB_37711889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11154318519030139) ^ 5577159259515069 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11154318519030139) ^ 3718106173010046 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11154318519030139) ^ 678814002 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11154318519030139) ^ 295777242 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_14584738097576557 : Nat.Prime 14584738097576557 := by
  apply lucas_primality 14584738097576557 (2 : ZMod 14584738097576557)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (13, 1), (1483998585427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (13, 1), (1483998585427, 1)] : List FactorBlock).map factorBlockValue).prod) = 14584738097576557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_1483998585427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14584738097576557) ^ 7292369048788278 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 4861579365858852 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 2083534013939508 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 1121902930582812 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 9828 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_15288154237780547 : Nat.Prime 15288154237780547 := by
  apply lucas_primality 15288154237780547 (2 : ZMod 15288154237780547)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (67, 1), (569, 1), (3783224567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (67, 1), (569, 1), (3783224567, 1)] : List FactorBlock).map factorBlockValue).prod) = 15288154237780547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_53
      · exact prime_oneHundredSixtyFB_67
      · exact prime_oneHundredSixtyFB_569
      · exact prime_oneHundredSixtyFB_3783224567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15288154237780547) ^ 7644077118890273 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15288154237780547) ^ 288455740335482 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15288154237780547) ^ 228181406534038 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15288154237780547) ^ 26868460874834 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15288154237780547) ^ 4041038 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_16170530168138809 : Nat.Prime 16170530168138809 := by
  apply lucas_primality 16170530168138809 (13 : ZMod 16170530168138809)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (8750286887521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (8750286887521, 1)] : List FactorBlock).map factorBlockValue).prod) = 16170530168138809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_8750286887521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 16170530168138809) ^ 8085265084069404 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 16170530168138809) ^ 5390176722712936 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 16170530168138809) ^ 2310075738305544 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 16170530168138809) ^ 1470048197103528 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 16170530168138809) ^ 1848 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_18042963338934497 : Nat.Prime 18042963338934497 := by
  apply lucas_primality 18042963338934497 (3 : ZMod 18042963338934497)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (43, 1), (2101129, 1), (6240749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (43, 1), (2101129, 1), (6240749, 1)] : List FactorBlock).map factorBlockValue).prod) = 18042963338934497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_2101129
      · exact prime_oneHundredSixtyFB_6240749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18042963338934497) ^ 9021481669467248 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18042963338934497) ^ 419603798579872 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18042963338934497) ^ 8587270624 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18042963338934497) ^ 2891153504 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_19676212285712849 : Nat.Prime 19676212285712849 := by
  apply lucas_primality 19676212285712849 (3 : ZMod 19676212285712849)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (705769, 1), (1742444437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (705769, 1), (1742444437, 1)] : List FactorBlock).map factorBlockValue).prod) = 19676212285712849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_705769
      · exact prime_oneHundredSixtyFB_1742444437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19676212285712849) ^ 9838106142856424 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19676212285712849) ^ 27879110992 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19676212285712849) ^ 11292304 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_29176035671262971 : Nat.Prime 29176035671262971 := by
  apply lucas_primality 29176035671262971 (6 : ZMod 29176035671262971)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (603739, 1), (98623627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (603739, 1), (98623627, 1)] : List FactorBlock).map factorBlockValue).prod) = 29176035671262971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_603739
      · exact prime_oneHundredSixtyFB_98623627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29176035671262971) ^ 14588017835631485 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 29176035671262971) ^ 5835207134252594 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 29176035671262971) ^ 4168005095894710 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 29176035671262971) ^ 48325577230 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 29176035671262971) ^ 295832110 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_32640857305682303 : Nat.Prime 32640857305682303 := by
  apply lucas_primality 32640857305682303 (5 : ZMod 32640857305682303)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (158450763619817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (158450763619817, 1)] : List FactorBlock).map factorBlockValue).prod) = 32640857305682303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_103
      · exact prime_oneHundredSixtyFB_158450763619817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 32640857305682303) ^ 16320428652841151 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 32640857305682303) ^ 316901527239634 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 32640857305682303) ^ 206 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_131
      · exact prime_oneHundredSixtyFB_170603
      · exact prime_oneHundredSixtyFB_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_47277277686818681 : Nat.Prime 47277277686818681 := by
  apply lucas_primality 47277277686818681 (6 : ZMod 47277277686818681)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (107, 1), (11046092917481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (107, 1), (11046092917481, 1)] : List FactorBlock).map factorBlockValue).prod) = 47277277686818681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_107
      · exact prime_oneHundredSixtyFB_11046092917481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 47277277686818681) ^ 23638638843409340 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 47277277686818681) ^ 9455455537363736 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 47277277686818681) ^ 441843716699240 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 47277277686818681) ^ 4280 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_49323882700265189 : Nat.Prime 49323882700265189 := by
  apply lucas_primality 49323882700265189 (2 : ZMod 49323882700265189)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (122327, 1), (100803344111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (122327, 1), (100803344111, 1)] : List FactorBlock).map factorBlockValue).prod) = 49323882700265189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_122327
      · exact prime_oneHundredSixtyFB_100803344111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49323882700265189) ^ 24661941350132594 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49323882700265189) ^ 403213376444 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49323882700265189) ^ 489308 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_53015135238325067 : Nat.Prime 53015135238325067 := by
  apply lucas_primality 53015135238325067 (2 : ZMod 53015135238325067)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) = 53015135238325067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_163
      · exact prime_oneHundredSixtyFB_9566065542823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53015135238325067) ^ 26507567619162533 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 3118537366960298 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 325246228455982 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 5542 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_139
      · exact prime_oneHundredSixtyFB_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_67764689244960619 : Nat.Prime 67764689244960619 := by
  apply lucas_primality 67764689244960619 (2 : ZMod 67764689244960619)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 2), (4637, 1), (229583491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 2), (4637, 1), (229583491, 1)] : List FactorBlock).map factorBlockValue).prod) = 67764689244960619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_103
      · exact prime_oneHundredSixtyFB_4637
      · exact prime_oneHundredSixtyFB_229583491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67764689244960619) ^ 33882344622480309 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67764689244960619) ^ 22588229748320206 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67764689244960619) ^ 657909604320006 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67764689244960619) ^ 14613907536114 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67764689244960619) ^ 295163598 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_31
      · exact prime_oneHundredSixtyFB_24841
      · exact prime_oneHundredSixtyFB_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_70931076648862813 : Nat.Prime 70931076648862813 := by
  apply lucas_primality 70931076648862813 (2 : ZMod 70931076648862813)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9323, 1), (10667, 1), (59437061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9323, 1), (10667, 1), (59437061, 1)] : List FactorBlock).map factorBlockValue).prod) = 70931076648862813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_9323
      · exact prime_oneHundredSixtyFB_10667
      · exact prime_oneHundredSixtyFB_59437061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70931076648862813) ^ 35465538324431406 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70931076648862813) ^ 23643692216287604 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70931076648862813) ^ 7608181556244 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70931076648862813) ^ 6649580636436 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70931076648862813) ^ 1193381292 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_83755445528838469 : Nat.Prime 83755445528838469 := by
  apply lucas_primality 83755445528838469 (2 : ZMod 83755445528838469)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (9365437, 1), (9678611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (9365437, 1), (9678611, 1)] : List FactorBlock).map factorBlockValue).prod) = 83755445528838469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_9365437
      · exact prime_oneHundredSixtyFB_9678611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83755445528838469) ^ 41877722764419234 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 83755445528838469) ^ 27918481842946156 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 83755445528838469) ^ 11965063646976924 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 83755445528838469) ^ 7614131411712588 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 83755445528838469) ^ 8943036564 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 83755445528838469) ^ 8653663788 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_97507418655314557 : Nat.Prime 97507418655314557 := by
  apply lucas_primality 97507418655314557 (6 : ZMod 97507418655314557)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (386934201013153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (386934201013153, 1)] : List FactorBlock).map factorBlockValue).prod) = 97507418655314557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_386934201013153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 97507418655314557) ^ 48753709327657278 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 97507418655314557) ^ 32502472885104852 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 97507418655314557) ^ 13929631236473508 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 97507418655314557) ^ 252 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_104997213222150383 : Nat.Prime 104997213222150383 := by
  apply lucas_primality 104997213222150383 (5 : ZMod 104997213222150383)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) = 104997213222150383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_1545121
      · exact prime_oneHundredSixtyFB_4853859953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 104997213222150383) ^ 52498606611075191 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 14999601888878626 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 67954039342 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 21631694 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_121197184259488681 : Nat.Prime 121197184259488681 := by
  apply lucas_primality 121197184259488681 (23 : ZMod 121197184259488681)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (79, 1), (131, 1), (9631, 1), (1447583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (79, 1), (131, 1), (9631, 1), (1447583, 1)] : List FactorBlock).map factorBlockValue).prod) = 121197184259488681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_79
      · exact prime_oneHundredSixtyFB_131
      · exact prime_oneHundredSixtyFB_9631
      · exact prime_oneHundredSixtyFB_1447583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 121197184259488681) ^ 60598592129744340 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 40399061419829560 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 24239436851897736 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 17313883465641240 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 1534141572904920 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 925169345492280 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 12584070632280 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 83723823960 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_139271123883117227 : Nat.Prime 139271123883117227 := by
  apply lucas_primality 139271123883117227 (2 : ZMod 139271123883117227)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (227, 1), (313, 1), (877, 1), (1116419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (227, 1), (313, 1), (877, 1), (1116419, 1)] : List FactorBlock).map factorBlockValue).prod) = 139271123883117227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_227
      · exact prime_oneHundredSixtyFB_313
      · exact prime_oneHundredSixtyFB_877
      · exact prime_oneHundredSixtyFB_1116419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139271123883117227) ^ 69635561941558613 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 19895874840445318 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 12661011262101566 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 10713163375624402 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 613529180101838 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 444955667358202 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 158804018110738 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 124748077454 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_161504144948665201 : Nat.Prime 161504144948665201 := by
  apply lucas_primality 161504144948665201 (13 : ZMod 161504144948665201)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (11, 1), (487, 1), (25123536953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (11, 1), (487, 1), (25123536953, 1)] : List FactorBlock).map factorBlockValue).prod) = 161504144948665201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_487
      · exact prime_oneHundredSixtyFB_25123536953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 161504144948665201) ^ 80752072474332600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 161504144948665201) ^ 53834714982888400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 161504144948665201) ^ 32300828989733040 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 161504144948665201) ^ 14682194995333200 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 161504144948665201) ^ 331630687779600 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 161504144948665201) ^ 6428400 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_185560283253726743 : Nat.Prime 185560283253726743 := by
  apply lucas_primality 185560283253726743 (5 : ZMod 185560283253726743)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2441, 1), (38009070719731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2441, 1), (38009070719731, 1)] : List FactorBlock).map factorBlockValue).prod) = 185560283253726743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_2441
      · exact prime_oneHundredSixtyFB_38009070719731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 185560283253726743) ^ 92780141626863371 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 185560283253726743) ^ 76018141439462 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 185560283253726743) ^ 4882 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_199539395747394767 : Nat.Prime 199539395747394767 := by
  apply lucas_primality 199539395747394767 (7 : ZMod 199539395747394767)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (839, 1), (4363, 1), (169287779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (839, 1), (4363, 1), (169287779, 1)] : List FactorBlock).map factorBlockValue).prod) = 199539395747394767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_839
      · exact prime_oneHundredSixtyFB_4363
      · exact prime_oneHundredSixtyFB_169287779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 199539395747394767) ^ 99769697873697383 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 199539395747394767) ^ 28505627963913538 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 199539395747394767) ^ 8675625902060642 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 199539395747394767) ^ 237830030688194 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 199539395747394767) ^ 45734447799082 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 199539395747394767) ^ 1178699354 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_229590316476973157 : Nat.Prime 229590316476973157 := by
  apply lucas_primality 229590316476973157 (2 : ZMod 229590316476973157)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (972840324054971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (972840324054971, 1)] : List FactorBlock).map factorBlockValue).prod) = 229590316476973157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_59
      · exact prime_oneHundredSixtyFB_972840324054971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229590316476973157) ^ 114795158238486578 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 229590316476973157) ^ 3891361296219884 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 229590316476973157) ^ 236 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_528310133400944501 : Nat.Prime 528310133400944501 := by
  apply lucas_primality 528310133400944501 (2 : ZMod 528310133400944501)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (71, 1), (139, 1), (76423, 1), (1400947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (71, 1), (139, 1), (76423, 1), (1400947, 1)] : List FactorBlock).map factorBlockValue).prod) = 528310133400944501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_139
      · exact prime_oneHundredSixtyFB_76423
      · exact prime_oneHundredSixtyFB_1400947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 528310133400944501) ^ 264155066700472250 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 528310133400944501) ^ 105662026680188900 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 528310133400944501) ^ 7440987794379500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 528310133400944501) ^ 3800792326625500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 528310133400944501) ^ 6912972971500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 528310133400944501) ^ 377109293500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_767131837000485961 : Nat.Prime 767131837000485961 := by
  apply lucas_primality 767131837000485961 (17 : ZMod 767131837000485961)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (73, 1), (80107, 1), (57536287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (73, 1), (80107, 1), (57536287, 1)] : List FactorBlock).map factorBlockValue).prod) = 767131837000485961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_73
      · exact prime_oneHundredSixtyFB_80107
      · exact prime_oneHundredSixtyFB_57536287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 767131837000485961) ^ 383565918500242980 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 767131837000485961) ^ 255710612333495320 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 767131837000485961) ^ 153426367400097192 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 767131837000485961) ^ 40375359842130840 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 767131837000485961) ^ 10508655301376520 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 767131837000485961) ^ 9576339608280 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (17 : ZMod 767131837000485961) ^ 13333009080 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_887669353177823149 : Nat.Prime 887669353177823149 := by
  apply lucas_primality 887669353177823149 (6 : ZMod 887669353177823149)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (144103, 1), (218641, 1), (2347823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (144103, 1), (218641, 1), (2347823, 1)] : List FactorBlock).map factorBlockValue).prod) = 887669353177823149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_144103
      · exact prime_oneHundredSixtyFB_218641
      · exact prime_oneHundredSixtyFB_2347823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 887669353177823149) ^ 443834676588911574 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 887669353177823149) ^ 295889784392607716 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 887669353177823149) ^ 6159964422516 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 887669353177823149) ^ 4059940053228 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 887669353177823149) ^ 378081888276 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_986477654005303781 : Nat.Prime 986477654005303781 := by
  apply lucas_primality 986477654005303781 (2 : ZMod 986477654005303781)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (49323882700265189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (49323882700265189, 1)] : List FactorBlock).map factorBlockValue).prod) = 986477654005303781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_49323882700265189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 986477654005303781) ^ 493238827002651890 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 986477654005303781) ^ 197295530801060756 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 986477654005303781) ^ 20 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1309234191118560457 : Nat.Prime 1309234191118560457 := by
  apply lucas_primality 1309234191118560457 (5 : ZMod 1309234191118560457)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (62731, 1), (869608720249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (62731, 1), (869608720249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1309234191118560457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_62731
      · exact prime_oneHundredSixtyFB_869608720249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1309234191118560457) ^ 654617095559280228 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1309234191118560457) ^ 436411397039520152 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1309234191118560457) ^ 20870609285976 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1309234191118560457) ^ 1505544 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_101
      · exact prime_oneHundredSixtyFB_191
      · exact prime_oneHundredSixtyFB_48017
      · exact prime_oneHundredSixtyFB_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3045429836125143989 : Nat.Prime 3045429836125143989 := by
  apply lucas_primality 3045429836125143989 (2 : ZMod 3045429836125143989)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (97, 1), (2819, 1), (151817, 1), (232153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (97, 1), (2819, 1), (151817, 1), (232153, 1)] : List FactorBlock).map factorBlockValue).prod) = 3045429836125143989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_79
      · exact prime_oneHundredSixtyFB_97
      · exact prime_oneHundredSixtyFB_2819
      · exact prime_oneHundredSixtyFB_151817
      · exact prime_oneHundredSixtyFB_232153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3045429836125143989) ^ 1522714918062571994 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3045429836125143989) ^ 38549744761077772 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3045429836125143989) ^ 31396183877578804 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3045429836125143989) ^ 1080322751374652 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3045429836125143989) ^ 20059873638164 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3045429836125143989) ^ 13118201514196 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3165334654942473973 : Nat.Prime 3165334654942473973 := by
  apply lucas_primality 3165334654942473973 (2 : ZMod 3165334654942473973)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (179, 1), (30073867051861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (179, 1), (30073867051861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3165334654942473973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_179
      · exact prime_oneHundredSixtyFB_30073867051861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3165334654942473973) ^ 1582667327471236986 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 1055111551647491324 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 452190664991781996 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 17683433826494268 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 105252 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_4552238527554537427 : Nat.Prime 4552238527554537427 := by
  apply lucas_primality 4552238527554537427 (2 : ZMod 4552238527554537427)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1363031, 1), (556631816341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1363031, 1), (556631816341, 1)] : List FactorBlock).map factorBlockValue).prod) = 4552238527554537427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_1363031
      · exact prime_oneHundredSixtyFB_556631816341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4552238527554537427) ^ 2276119263777268713 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4552238527554537427) ^ 1517412842518179142 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4552238527554537427) ^ 3339790898046 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4552238527554537427) ^ 8178186 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_6595360786036901363 : Nat.Prime 6595360786036901363 := by
  apply lucas_primality 6595360786036901363 (2 : ZMod 6595360786036901363)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1720217, 1), (174274016963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1720217, 1), (174274016963, 1)] : List FactorBlock).map factorBlockValue).prod) = 6595360786036901363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_1720217
      · exact prime_oneHundredSixtyFB_174274016963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6595360786036901363) ^ 3297680393018450681 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595360786036901363) ^ 599578253276081942 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595360786036901363) ^ 3834028373186 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595360786036901363) ^ 37844774 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_13190721572073802727 : Nat.Prime 13190721572073802727 := by
  apply lucas_primality 13190721572073802727 (5 : ZMod 13190721572073802727)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6595360786036901363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6595360786036901363, 1)] : List FactorBlock).map factorBlockValue).prod) = 13190721572073802727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_6595360786036901363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 13190721572073802727) ^ 6595360786036901363 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 13190721572073802727) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_26866939219178079023 : Nat.Prime 26866939219178079023 := by
  apply lucas_primality 26866939219178079023 (5 : ZMod 26866939219178079023)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443, 1), (2829383, 1), (10717481219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443, 1), (2829383, 1), (10717481219, 1)] : List FactorBlock).map factorBlockValue).prod) = 26866939219178079023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_443
      · exact prime_oneHundredSixtyFB_2829383
      · exact prime_oneHundredSixtyFB_10717481219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26866939219178079023) ^ 13433469609589039511 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 26866939219178079023) ^ 60647718327715754 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 26866939219178079023) ^ 9495688360034 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 26866939219178079023) ^ 2506833338 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_34246257432295613279 : Nat.Prime 34246257432295613279 := by
  apply lucas_primality 34246257432295613279 (7 : ZMod 34246257432295613279)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (90011, 1), (344003137333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (90011, 1), (344003137333, 1)] : List FactorBlock).map factorBlockValue).prod) = 34246257432295613279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_79
      · exact prime_oneHundredSixtyFB_90011
      · exact prime_oneHundredSixtyFB_344003137333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34246257432295613279) ^ 17123128716147806639 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 34246257432295613279) ^ 4892322490327944754 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 34246257432295613279) ^ 433496929522729282 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 34246257432295613279) ^ 380467469890298 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (7 : ZMod 34246257432295613279) ^ 99552166 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_2063
      · exact prime_oneHundredSixtyFB_15269
      · exact prime_oneHundredSixtyFB_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_62623543778154303929 : Nat.Prime 62623543778154303929 := by
  apply lucas_primality 62623543778154303929 (3 : ZMod 62623543778154303929)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (701, 1), (8011, 1), (34807, 1), (482501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (701, 1), (8011, 1), (34807, 1), (482501, 1)] : List FactorBlock).map factorBlockValue).prod) = 62623543778154303929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_83
      · exact prime_oneHundredSixtyFB_701
      · exact prime_oneHundredSixtyFB_8011
      · exact prime_oneHundredSixtyFB_34807
      · exact prime_oneHundredSixtyFB_482501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62623543778154303929) ^ 31311771889077151964 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 62623543778154303929) ^ 754500527447642216 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 62623543778154303929) ^ 89334584562274328 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 62623543778154303929) ^ 7817194330065448 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 62623543778154303929) ^ 1799165219012104 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 62623543778154303929) ^ 129789459043928 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_108276953428340218793 : Nat.Prime 108276953428340218793 := by
  apply lucas_primality 108276953428340218793 (3 : ZMod 108276953428340218793)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (70201, 1), (328429, 1), (587031281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (70201, 1), (328429, 1), (587031281, 1)] : List FactorBlock).map factorBlockValue).prod) = 108276953428340218793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_70201
      · exact prime_oneHundredSixtyFB_328429
      · exact prime_oneHundredSixtyFB_587031281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 108276953428340218793) ^ 54138476714170109396 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 108276953428340218793) ^ 1542384772700392 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 108276953428340218793) ^ 329681463659848 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 108276953428340218793) ^ 184448353832 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_178257538762268747531 : Nat.Prime 178257538762268747531 := by
  apply lucas_primality 178257538762268747531 (2 : ZMod 178257538762268747531)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (250155133, 1), (10179828163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (250155133, 1), (10179828163, 1)] : List FactorBlock).map factorBlockValue).prod) = 178257538762268747531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_250155133
      · exact prime_oneHundredSixtyFB_10179828163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178257538762268747531) ^ 89128769381134373765 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178257538762268747531) ^ 35651507752453749506 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178257538762268747531) ^ 25465362680324106790 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178257538762268747531) ^ 712587971410 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178257538762268747531) ^ 17510859310 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_250218963210430951553 : Nat.Prime 250218963210430951553 := by
  apply lucas_primality 250218963210430951553 (3 : ZMod 250218963210430951553)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3613349, 1), (541003830541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3613349, 1), (541003830541, 1)] : List FactorBlock).map factorBlockValue).prod) = 250218963210430951553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3613349
      · exact prime_oneHundredSixtyFB_541003830541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 250218963210430951553) ^ 125109481605215475776 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 250218963210430951553) ^ 69248490309248 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 250218963210430951553) ^ 462508672 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_695450024211916627019 : Nat.Prime 695450024211916627019 := by
  apply lucas_primality 695450024211916627019 (2 : ZMod 695450024211916627019)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) = 695450024211916627019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_2500999
      · exact prime_oneHundredSixtyFB_139034446677491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 695450024211916627019) ^ 347725012105958313509 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 278068893354982 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 5001998 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_71
      · exact prime_oneHundredSixtyFB_199
      · exact prime_oneHundredSixtyFB_52864081
      · exact prime_oneHundredSixtyFB_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2319576689632570840429 : Nat.Prime 2319576689632570840429 := by
  apply lucas_primality 2319576689632570840429 (2 : ZMod 2319576689632570840429)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (47, 1), (509, 1), (734546280944473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (47, 1), (509, 1), (734546280944473, 1)] : List FactorBlock).map factorBlockValue).prod) = 2319576689632570840429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_47
      · exact prime_oneHundredSixtyFB_509
      · exact prime_oneHundredSixtyFB_734546280944473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2319576689632570840429) ^ 1159788344816285420214 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319576689632570840429) ^ 773192229877523613476 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319576689632570840429) ^ 210870608148415530948 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319576689632570840429) ^ 49352695524097251924 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319576689632570840429) ^ 4557125126979510492 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319576689632570840429) ^ 3157836 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2949850565855340252697 : Nat.Prime 2949850565855340252697 := by
  apply lucas_primality 2949850565855340252697 (5 : ZMod 2949850565855340252697)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (4552238527554537427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (4552238527554537427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2949850565855340252697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_4552238527554537427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2949850565855340252697) ^ 1474925282927670126348 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2949850565855340252697) ^ 983283521951780084232 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2949850565855340252697) ^ 648 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_3321529070241708699701 : Nat.Prime 3321529070241708699701 := by
  apply lucas_primality 3321529070241708699701 (2 : ZMod 3321529070241708699701)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (179, 1), (185560283253726743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (179, 1), (185560283253726743, 1)] : List FactorBlock).map factorBlockValue).prod) = 3321529070241708699701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_179
      · exact prime_oneHundredSixtyFB_185560283253726743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3321529070241708699701) ^ 1660764535120854349850 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3321529070241708699701) ^ 664305814048341739940 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3321529070241708699701) ^ 18556028325372674300 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3321529070241708699701) ^ 17900 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_4162625474848011401017 : Nat.Prime 4162625474848011401017 := by
  apply lucas_primality 4162625474848011401017 (11 : ZMod 4162625474848011401017)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19391, 1), (145349, 1), (61538065751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19391, 1), (145349, 1), (61538065751, 1)] : List FactorBlock).map factorBlockValue).prod) = 4162625474848011401017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_19391
      · exact prime_oneHundredSixtyFB_145349
      · exact prime_oneHundredSixtyFB_61538065751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4162625474848011401017) ^ 2081312737424005700508 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 4162625474848011401017) ^ 1387541824949337133672 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 4162625474848011401017) ^ 214667911652210376 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 4162625474848011401017) ^ 28638831191463384 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 4162625474848011401017) ^ 67643099016 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_9557346059326019093897 : Nat.Prime 9557346059326019093897 := by
  apply lucas_primality 9557346059326019093897 (3 : ZMod 9557346059326019093897)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (607, 1), (4217, 1), (466718517702823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (607, 1), (4217, 1), (466718517702823, 1)] : List FactorBlock).map factorBlockValue).prod) = 9557346059326019093897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_607
      · exact prime_oneHundredSixtyFB_4217
      · exact prime_oneHundredSixtyFB_466718517702823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9557346059326019093897) ^ 4778673029663009546948 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9557346059326019093897) ^ 15745215913222436728 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9557346059326019093897) ^ 2266385121964908488 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9557346059326019093897) ^ 20477752 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_19087120873294101673673 : Nat.Prime 19087120873294101673673 := by
  apply lucas_primality 19087120873294101673673 (5 : ZMod 19087120873294101673673)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (53, 1), (59, 1), (89009, 1), (779284339133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (53, 1), (59, 1), (89009, 1), (779284339133, 1)] : List FactorBlock).map factorBlockValue).prod) = 19087120873294101673673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_53
      · exact prime_oneHundredSixtyFB_59
      · exact prime_oneHundredSixtyFB_89009
      · exact prime_oneHundredSixtyFB_779284339133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19087120873294101673673) ^ 9543560436647050836836 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19087120873294101673673) ^ 1735192806663100152152 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19087120873294101673673) ^ 360134356099888710824 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19087120873294101673673) ^ 323510523276171214808 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19087120873294101673673) ^ 214440347305262408 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19087120873294101673673) ^ 24493140584 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_22012051700405730964789 : Nat.Prime 22012051700405730964789 := by
  apply lucas_primality 22012051700405730964789 (6 : ZMod 22012051700405730964789)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 8), (15227, 1), (527581, 1), (104406371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 8), (15227, 1), (527581, 1), (104406371, 1)] : List FactorBlock).map factorBlockValue).prod) = 22012051700405730964789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_15227
      · exact prime_oneHundredSixtyFB_527581
      · exact prime_oneHundredSixtyFB_104406371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22012051700405730964789) ^ 11006025850202865482394 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 22012051700405730964789) ^ 7337350566801910321596 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 22012051700405730964789) ^ 1445593465581252444 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 22012051700405730964789) ^ 41722601269578948 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 22012051700405730964789) ^ 210830541178428 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_65365831068731828517637 : Nat.Prime 65365831068731828517637 := by
  apply lucas_primality 65365831068731828517637 (2 : ZMod 65365831068731828517637)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (7741, 1), (18042963338934497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (7741, 1), (18042963338934497, 1)] : List FactorBlock).map factorBlockValue).prod) = 65365831068731828517637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_7741
      · exact prime_oneHundredSixtyFB_18042963338934497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65365831068731828517637) ^ 32682915534365914258818 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65365831068731828517637) ^ 21788610356243942839212 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65365831068731828517637) ^ 5028140851440909885972 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65365831068731828517637) ^ 8444106842621344596 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65365831068731828517637) ^ 3622788 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_75184590899062904152867 : Nat.Prime 75184590899062904152867 := by
  apply lucas_primality 75184590899062904152867 (2 : ZMod 75184590899062904152867)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 2), (607, 1), (1031, 1), (1543, 1), (6414582947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 2), (607, 1), (1031, 1), (1543, 1), (6414582947, 1)] : List FactorBlock).map factorBlockValue).prod) = 75184590899062904152867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_607
      · exact prime_oneHundredSixtyFB_1031
      · exact prime_oneHundredSixtyFB_1543
      · exact prime_oneHundredSixtyFB_6414582947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75184590899062904152867) ^ 37592295449531452076433 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 25061530299687634717622 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 10740655842723272021838 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 4422622994062523773698 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 123862587972097041438 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 72923948495696318286 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 48726241671460080462 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75184590899062904152867) ^ 11720885289078 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_161123780116753949377241 : Nat.Prime 161123780116753949377241 := by
  apply lucas_primality 161123780116753949377241 (6 : ZMod 161123780116753949377241)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (204719, 1), (19676212285712849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (204719, 1), (19676212285712849, 1)] : List FactorBlock).map factorBlockValue).prod) = 161123780116753949377241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_204719
      · exact prime_oneHundredSixtyFB_19676212285712849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 161123780116753949377241) ^ 80561890058376974688620 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 161123780116753949377241) ^ 32224756023350789875448 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 161123780116753949377241) ^ 787048491428513960 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (6 : ZMod 161123780116753949377241) ^ 8188760 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_363690497301491172040717 : Nat.Prime 363690497301491172040717 := by
  apply lucas_primality 363690497301491172040717 (2 : ZMod 363690497301491172040717)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) = 363690497301491172040717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_157
      · exact prime_oneHundredSixtyFB_13511921
      · exact prime_oneHundredSixtyFB_14286766865669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 363690497301491172040717) ^ 181845248650745586020358 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 121230165767163724013572 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 2316499982812045681788 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 26916268774920396 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 25456459164 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_377719540769508884552813 : Nat.Prime 377719540769508884552813 := by
  apply lucas_primality 377719540769508884552813 (2 : ZMod 377719540769508884552813)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (199, 1), (10037, 1), (47277277686818681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (199, 1), (10037, 1), (47277277686818681, 1)] : List FactorBlock).map factorBlockValue).prod) = 377719540769508884552813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_199
      · exact prime_oneHundredSixtyFB_10037
      · exact prime_oneHundredSixtyFB_47277277686818681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 377719540769508884552813) ^ 188859770384754442276406 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719540769508884552813) ^ 1898088144570396404788 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719540769508884552813) ^ 37632713038707670076 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719540769508884552813) ^ 7989452 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_418512662850455296162327 : Nat.Prime 418512662850455296162327 := by
  apply lucas_primality 418512662850455296162327 (10 : ZMod 418512662850455296162327)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3321529070241708699701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3321529070241708699701, 1)] : List FactorBlock).map factorBlockValue).prod) = 418512662850455296162327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_3321529070241708699701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 418512662850455296162327) ^ 209256331425227648081163 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (10 : ZMod 418512662850455296162327) ^ 139504220950151765387442 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (10 : ZMod 418512662850455296162327) ^ 59787523264350756594618 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (10 : ZMod 418512662850455296162327) ^ 126 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_448290027505721063125657 : Nat.Prime 448290027505721063125657 := by
  apply lucas_primality 448290027505721063125657 (5 : ZMod 448290027505721063125657)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (17, 1), (21017, 1), (5808790066327169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (17, 1), (21017, 1), (5808790066327169, 1)] : List FactorBlock).map factorBlockValue).prod) = 448290027505721063125657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_21017
      · exact prime_oneHundredSixtyFB_5808790066327169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 448290027505721063125657) ^ 224145013752860531562828 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 149430009168573687708552 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 26370001617983591948568 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 21329877123553364568 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 77174424 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_710593009332886013740657 : Nat.Prime 710593009332886013740657 := by
  apply lucas_primality 710593009332886013740657 (5 : ZMod 710593009332886013740657)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 2), (15817, 1), (1769293600347029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 2), (15817, 1), (1769293600347029, 1)] : List FactorBlock).map factorBlockValue).prod) = 710593009332886013740657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_23
      · exact prime_oneHundredSixtyFB_15817
      · exact prime_oneHundredSixtyFB_1769293600347029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 710593009332886013740657) ^ 355296504666443006870328 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 236864336444295337913552 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 30895348231864609293072 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 44925903100011760368 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 401625264 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1307573264507120410334201 : Nat.Prime 1307573264507120410334201 := by
  apply lucas_primality 1307573264507120410334201 (3 : ZMod 1307573264507120410334201)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (78059, 1), (83755445528838469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (78059, 1), (83755445528838469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1307573264507120410334201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_78059
      · exact prime_oneHundredSixtyFB_83755445528838469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1307573264507120410334201) ^ 653786632253560205167100 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1307573264507120410334201) ^ 261514652901424082066840 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1307573264507120410334201) ^ 16751089105767693800 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1307573264507120410334201) ^ 15611800 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1454761989205964688162869 : Nat.Prime 1454761989205964688162869 := by
  apply lucas_primality 1454761989205964688162869 (2 : ZMod 1454761989205964688162869)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454761989205964688162869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_363690497301491172040717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1454761989205964688162869) ^ 727380994602982344081434 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454761989205964688162869) ^ 4 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_1741396719567433404234839 : Nat.Prime 1741396719567433404234839 := by
  apply lucas_primality 1741396719567433404234839 (11 : ZMod 1741396719567433404234839)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (333787, 1), (275681563, 1), (9462166499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (333787, 1), (275681563, 1), (9462166499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1741396719567433404234839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_333787
      · exact prime_oneHundredSixtyFB_275681563
      · exact prime_oneHundredSixtyFB_9462166499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1741396719567433404234839) ^ 870698359783716702117419 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1741396719567433404234839) ^ 5217089699621115874 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1741396719567433404234839) ^ 6316696338403426 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1741396719567433404234839) ^ 184037843738162 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_2676060682394946572945773 : Nat.Prime 2676060682394946572945773 := by
  apply lucas_primality 2676060682394946572945773 (2 : ZMod 2676060682394946572945773)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (233, 1), (5233, 1), (2903136834171983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (233, 1), (5233, 1), (2903136834171983, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676060682394946572945773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_233
      · exact prime_oneHundredSixtyFB_5233
      · exact prime_oneHundredSixtyFB_2903136834171983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2676060682394946572945773) ^ 1338030341197473286472886 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2676060682394946572945773) ^ 892020227464982190981924 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2676060682394946572945773) ^ 382294383199278081849396 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2676060682394946572945773) ^ 11485238980235822201484 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2676060682394946572945773) ^ 511381747065726461484 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2676060682394946572945773) ^ 921782484 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_20846671970074012387240231 : Nat.Prime 20846671970074012387240231 := by
  apply lucas_primality 20846671970074012387240231 (3 : ZMod 20846671970074012387240231)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (29, 2), (401, 1), (5813989, 1), (2664705773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (29, 2), (401, 1), (5813989, 1), (2664705773, 1)] : List FactorBlock).map factorBlockValue).prod) = 20846671970074012387240231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_29
      · exact prime_oneHundredSixtyFB_401
      · exact prime_oneHundredSixtyFB_5813989
      · exact prime_oneHundredSixtyFB_2664705773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20846671970074012387240231) ^ 10423335985037006193620115 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 6948890656691337462413410 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 4169334394014802477448046 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 2978095995724858912462890 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 1097193261582842757223170 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 718850757588759047835870 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 51986713142329207948230 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 3585605677973249070 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20846671970074012387240231) ^ 7823254702752510 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_152182382507201599679660383 : Nat.Prime 152182382507201599679660383 := by
  apply lucas_primality 152182382507201599679660383 (3 : ZMod 152182382507201599679660383)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (1103, 1), (178257538762268747531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (1103, 1), (178257538762268747531, 1)] : List FactorBlock).map factorBlockValue).prod) = 152182382507201599679660383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_43
      · exact prime_oneHundredSixtyFB_1103
      · exact prime_oneHundredSixtyFB_178257538762268747531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 152182382507201599679660383) ^ 76091191253600799839830191 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 152182382507201599679660383) ^ 50727460835733866559886794 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 152182382507201599679660383) ^ 3539125174586083713480474 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 152182382507201599679660383) ^ 137971335001996010588994 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 152182382507201599679660383) ^ 853722 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_174182966350323746226351617 : Nat.Prime 174182966350323746226351617 := by
  apply lucas_primality 174182966350323746226351617 (3 : ZMod 174182966350323746226351617)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 1), (24229, 1), (4744163, 1), (227665528093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 1), (24229, 1), (4744163, 1), (227665528093, 1)] : List FactorBlock).map factorBlockValue).prod) = 174182966350323746226351617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_13
      · exact prime_oneHundredSixtyFB_24229
      · exact prime_oneHundredSixtyFB_4744163
      · exact prime_oneHundredSixtyFB_227665528093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 174182966350323746226351617) ^ 87091483175161873113175808 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174182966350323746226351617) ^ 13398689719255672786642432 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174182966350323746226351617) ^ 7189028286364428834304 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174182966350323746226351617) ^ 36715215381580216832 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174182966350323746226351617) ^ 765082741376512 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_181364047417499125984485001 : Nat.Prime 181364047417499125984485001 := by
  apply lucas_primality 181364047417499125984485001 (14 : ZMod 181364047417499125984485001)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 4), (19, 1), (141871, 1), (1887283, 1), (2376707197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 4), (19, 1), (141871, 1), (1887283, 1), (2376707197, 1)] : List FactorBlock).map factorBlockValue).prod) = 181364047417499125984485001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_141871
      · exact prime_oneHundredSixtyFB_1887283
      · exact prime_oneHundredSixtyFB_2376707197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 181364047417499125984485001) ^ 90682023708749562992242500 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 181364047417499125984485001) ^ 60454682472499708661495000 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 181364047417499125984485001) ^ 36272809483499825196897000 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 181364047417499125984485001) ^ 9545476179868375051815000 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 181364047417499125984485001) ^ 1278372940329589035000 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 181364047417499125984485001) ^ 96097960622492295000 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (14 : ZMod 181364047417499125984485001) ^ 76308957050505000 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_273752100515848897831863757 : Nat.Prime 273752100515848897831863757 := by
  apply lucas_primality 273752100515848897831863757 (5 : ZMod 273752100515848897831863757)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (349, 1), (65365831068731828517637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (349, 1), (65365831068731828517637, 1)] : List FactorBlock).map factorBlockValue).prod) = 273752100515848897831863757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_349
      · exact prime_oneHundredSixtyFB_65365831068731828517637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 273752100515848897831863757) ^ 136876050257924448915931878 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 273752100515848897831863757) ^ 91250700171949632610621252 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 273752100515848897831863757) ^ 784389972824781942211644 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 273752100515848897831863757) ^ 4188 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_896505694106405632236103583 : Nat.Prime 896505694106405632236103583 := by
  apply lucas_primality 896505694106405632236103583 (5 : ZMod 896505694106405632236103583)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1427, 1), (41522732507, 1), (7565073605519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1427, 1), (41522732507, 1), (7565073605519, 1)] : List FactorBlock).map factorBlockValue).prod) = 896505694106405632236103583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_1427
      · exact prime_oneHundredSixtyFB_41522732507
      · exact prime_oneHundredSixtyFB_7565073605519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 896505694106405632236103583) ^ 448252847053202816118051791 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 896505694106405632236103583) ^ 628245055435462951812266 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 896505694106405632236103583) ^ 21590720070151226 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 896505694106405632236103583) ^ 118505878574978 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_4171314503
      · exact prime_oneHundredSixtyFB_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_7566508058258063536072714243 : Nat.Prime 7566508058258063536072714243 := by
  apply lucas_primality 7566508058258063536072714243 (3 : ZMod 7566508058258063536072714243)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7566508058258063536072714243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_1277
      · exact prime_oneHundredSixtyFB_38153
      · exact prime_oneHundredSixtyFB_45994279
      · exact prime_oneHundredSixtyFB_2977549837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7566508058258063536072714243) ^ 3783254029129031768036357121 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 2522169352752687845357571414 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 1080929722608294790867530606 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 5925221658776870427621546 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 198320133626662740441714 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 164509765622330193198 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 2541186032970525066 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_12610846763763439226787857069 : Nat.Prime 12610846763763439226787857069 := by
  apply lucas_primality 12610846763763439226787857069 (2 : ZMod 12610846763763439226787857069)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 12610846763763439226787857069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_89
      · exact prime_oneHundredSixtyFB_347
      · exact prime_oneHundredSixtyFB_2755243
      · exact prime_oneHundredSixtyFB_37051420944511243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12610846763763439226787857069) ^ 6305423381881719613393928534 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 141694907458016171087504012 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 36342497878280804688149444 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 4577036132117362870276 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 340360678276 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_15763558454704299033484821337 : Nat.Prime 15763558454704299033484821337 := by
  apply lucas_primality 15763558454704299033484821337 (5 : ZMod 15763558454704299033484821337)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 15763558454704299033484821337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_607213
      · exact prime_oneHundredSixtyFB_1081687868363620552253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15763558454704299033484821337) ^ 7881779227352149516742410668 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15763558454704299033484821337) ^ 5254519484901433011161607112 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15763558454704299033484821337) ^ 25960508840726893254072 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15763558454704299033484821337) ^ 14573112 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_23645337682056448550227232011 : Nat.Prime 23645337682056448550227232011 := by
  apply lucas_primality 23645337682056448550227232011 (3 : ZMod 23645337682056448550227232011)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056448550227232011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_3
      · exact prime_oneHundredSixtyFB_5
      · exact prime_oneHundredSixtyFB_11
      · exact prime_oneHundredSixtyFB_461
      · exact prime_oneHundredSixtyFB_69997
      · exact prime_oneHundredSixtyFB_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23645337682056448550227232011) ^ 11822668841028224275113616005 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 7881779227352149516742410670 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 4729067536411289710045446402 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 2149576152914222595475202910 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 51291404950230907918063410 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 337805015672906675289330 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 10648643610 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_47290675364112897100454464013 : Nat.Prime 47290675364112897100454464013 := by
  apply lucas_primality 47290675364112897100454464013 (2 : ZMod 47290675364112897100454464013)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112897100454464013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_17
      · exact prime_oneHundredSixtyFB_521
      · exact prime_oneHundredSixtyFB_23096547757
      · exact prime_oneHundredSixtyFB_57793874370247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47290675364112897100454464013) ^ 23645337682056448550227232006 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 2781804433183111594144380236 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 90769050602903833206246572 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 2047521381189110716 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 818264493934996 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_94581350728225794200908928027 : Nat.Prime 94581350728225794200908928027 := by
  apply lucas_primality 94581350728225794200908928027 (2 : ZMod 94581350728225794200908928027)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47290675364112897100454464013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47290675364112897100454464013, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225794200908928027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_47290675364112897100454464013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 94581350728225794200908928027) ^ 47290675364112897100454464013 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (2 : ZMod 94581350728225794200908928027) ^ 2 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFB_94581350728225794200908928033 : Nat.Prime 94581350728225794200908928033 := by
  apply lucas_primality 94581350728225794200908928033 (3 : ZMod 94581350728225794200908928033)
  · rw [← oneHundredSixtyFBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225794200908928033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFB_2
      · exact prime_oneHundredSixtyFB_7
      · exact prime_oneHundredSixtyFB_19
      · exact prime_oneHundredSixtyFB_41
      · exact prime_oneHundredSixtyFB_397
      · exact prime_oneHundredSixtyFB_13617913
      · exact prime_oneHundredSixtyFB_100257985466497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94581350728225794200908928033) ^ 47290675364112897100454464016 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 94581350728225794200908928033) ^ 13511621532603684885844132576 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 94581350728225794200908928033) ^ 4977965827801357589521522528 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 94581350728225794200908928033) ^ 2306862212883555956119729952 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 94581350728225794200908928033) ^ 238240178156740035770551456 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 94581350728225794200908928033) ^ 6945363120488858623264 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide
    · change (3 : ZMod 94581350728225794200908928033) ^ 943379724698656 ≠ 1
      rw [← oneHundredSixtyFBFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856000 : Nat.totient 189162701456451588401817856000 = 75664639013442998702653440000 := by
  rw [← show ((([(2, 11), (5, 3), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_171401, prime_oneHundredSixtyFB_714027719, prime_oneHundredSixtyFB_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856001 : Nat.totient 189162701456451588401817856001 = 162119418092791390991921659200 := by
  rw [← show ((([(7, 1), (8543, 1), (229739, 1), (456151, 1), (30184480354109, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_8543, prime_oneHundredSixtyFB_229739, prime_oneHundredSixtyFB_456151, prime_oneHundredSixtyFB_30184480354109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856002 : Nat.totient 189162701456451588401817856002 = 63042710711020753072083832320 := by
  rw [← show ((([(2, 1), (3, 1), (5843, 1), (86161, 1), (62623543778154303929, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5843, prime_oneHundredSixtyFB_86161, prime_oneHundredSixtyFB_62623543778154303929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856003 : Nat.totient 189162701456451588401817856003 = 146070320047602774432111360000 := by
  rw [← show ((([(11, 1), (13, 1), (23, 1), (31, 1), (307, 1), (389, 1), (11987, 1), (208367, 1), (6219887351, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_23, prime_oneHundredSixtyFB_31, prime_oneHundredSixtyFB_307, prime_oneHundredSixtyFB_389, prime_oneHundredSixtyFB_11987, prime_oneHundredSixtyFB_208367, prime_oneHundredSixtyFB_6219887351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856004 : Nat.totient 189162701456451588401817856004 = 91970933733546350449539288960 := by
  rw [← show ((([(2, 2), (37, 1), (1699, 1), (276099113611, 1), (2724679354157, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_37, prime_oneHundredSixtyFB_1699, prime_oneHundredSixtyFB_276099113611, prime_oneHundredSixtyFB_2724679354157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856005 : Nat.totient 189162701456451588401817856005 = 100876015149447376508787615744 := by
  rw [← show ((([(3, 2), (5, 1), (9377, 1), (448290027505721063125657, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_9377, prime_oneHundredSixtyFB_448290027505721063125657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856006 : Nat.totient 189162701456451588401817856006 = 94581347778375228345536612208 := by
  rw [← show ((([(2, 1), (32063099, 1), (2949850565855340252697, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_32063099, prime_oneHundredSixtyFB_2949850565855340252697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856007 : Nat.totient 189162701456451588401817856007 = 179206769800822005743493363264 := by
  rw [← show ((([(19, 1), (6700100600437, 1), (1485937637257769, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_19, prime_oneHundredSixtyFB_6700100600437, prime_oneHundredSixtyFB_1485937637257769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856008 : Nat.totient 189162701456451588401817856008 = 52727561344961904891540750336 := by
  rw [← show ((([(2, 3), (3, 1), (7, 2), (47, 1), (313, 1), (55413389, 1), (197320078064177, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_47, prime_oneHundredSixtyFB_313, prime_oneHundredSixtyFB_55413389, prime_oneHundredSixtyFB_197320078064177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856009 : Nat.totient 189162701456451588401817856009 = 188791065049805435775977164032 := by
  rw [← show ((([(509, 1), (418664849, 1), (887669353177823149, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_509, prime_oneHundredSixtyFB_418664849, prime_oneHundredSixtyFB_887669353177823149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856010 : Nat.totient 189162701456451588401817856010 = 72982664068293201345537722112 := by
  rw [← show ((([(2, 1), (5, 1), (29, 1), (997, 1), (1953042799, 1), (334989034308223, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_29, prime_oneHundredSixtyFB_997, prime_oneHundredSixtyFB_1953042799, prime_oneHundredSixtyFB_334989034308223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856011 : Nat.totient 189162701456451588401817856011 = 126108467637612072325042901832 := by
  rw [← show ((([(3, 1), (5652898804283, 1), (11154318519030139, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5652898804283, prime_oneHundredSixtyFB_11154318519030139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856012 : Nat.totient 189162701456451588401817856012 = 94500584803605626600077516800 := by
  rw [← show ((([(2, 2), (1451, 1), (6689, 1), (71999, 1), (676337, 1), (100059262279, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_1451, prime_oneHundredSixtyFB_6689, prime_oneHundredSixtyFB_71999, prime_oneHundredSixtyFB_676337, prime_oneHundredSixtyFB_100059262279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856013 : Nat.totient 189162701456451588401817856013 = 188266195762345182769581752220 := by
  rw [← show ((([(211, 1), (896505694106405632236103583, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_211, prime_oneHundredSixtyFB_896505694106405632236103583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856014 : Nat.totient 189162701456451588401817856014 = 53950146517891092081801427200 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (17, 1), (829311991, 1), (67764689244960619, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_17, prime_oneHundredSixtyFB_829311991, prime_oneHundredSixtyFB_67764689244960619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856015 : Nat.totient 189162701456451588401817856015 = 127513063759812645601806200064 := by
  rw [← show ((([(5, 1), (7, 1), (59, 1), (69967783, 1), (1309234191118560457, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_59, prime_oneHundredSixtyFB_69967783, prime_oneHundredSixtyFB_1309234191118560457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856016 : Nat.totient 189162701456451588401817856016 = 87305862210669963877762087296 := by
  rw [← show ((([(2, 4), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856017 : Nat.totient 189162701456451588401817856017 = 123895897226202100819728384000 := by
  rw [← show ((([(3, 1), (103, 1), (127, 1), (25409, 1), (198515441, 1), (955633666051, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_103, prime_oneHundredSixtyFB_127, prime_oneHundredSixtyFB_25409, prime_oneHundredSixtyFB_198515441, prime_oneHundredSixtyFB_955633666051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856018 : Nat.totient 189162701456451588401817856018 = 94581350728209617821745750400 := by
  rw [← show ((([(2, 1), (5848995038801, 1), (16170530168138809, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5848995038801, prime_oneHundredSixtyFB_16170530168138809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856019 : Nat.totient 189162701456451588401817856019 = 184453577702973082527668736000 := by
  rw [← show ((([(71, 1), (101, 1), (983, 1), (17657, 1), (3780113, 1), (402050464063, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_71, prime_oneHundredSixtyFB_101, prime_oneHundredSixtyFB_983, prime_oneHundredSixtyFB_17657, prime_oneHundredSixtyFB_3780113, prime_oneHundredSixtyFB_402050464063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856020 : Nat.totient 189162701456451588401817856020 = 49732852754133087653981002752 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_89, prime_oneHundredSixtyFB_347, prime_oneHundredSixtyFB_2755243, prime_oneHundredSixtyFB_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856021 : Nat.totient 189162701456451588401817856021 = 189162701456380654658316741792 := by
  rw [← show ((([(2666852251417, 1), (70931076648862813, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2666852251417, prime_oneHundredSixtyFB_70931076648862813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856022 : Nat.totient 189162701456451588401817856022 = 81069729034420473996978868200 := by
  rw [← show ((([(2, 1), (7, 1), (502908851, 1), (26866939219178079023, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_502908851, prime_oneHundredSixtyFB_26866939219178079023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856023 : Nat.totient 189162701456451588401817856023 = 121315249704510728479989411840 := by
  rw [← show ((([(3, 3), (41, 1), (163, 1), (283, 1), (337, 1), (719, 1), (15288154237780547, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_41, prime_oneHundredSixtyFB_163, prime_oneHundredSixtyFB_283, prime_oneHundredSixtyFB_337, prime_oneHundredSixtyFB_719, prime_oneHundredSixtyFB_15288154237780547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856024 : Nat.totient 189162701456451588401817856024 = 94581350728013731875911310912 := by
  rw [← show ((([(2, 3), (446011079209, 1), (53015135238325067, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_446011079209, prime_oneHundredSixtyFB_53015135238325067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856025 : Nat.totient 189162701456451588401817856025 = 134976998428427192934274560000 := by
  rw [← show ((([(5, 2), (11, 1), (53, 1), (846733, 1), (100123619, 1), (153088976401, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_53, prime_oneHundredSixtyFB_846733, prime_oneHundredSixtyFB_100123619, prime_oneHundredSixtyFB_153088976401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856026 : Nat.totient 189162701456451588401817856026 = 56839236494995696947507149760 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (23, 1), (191, 1), (377719540769508884552813, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_19, prime_oneHundredSixtyFB_23, prime_oneHundredSixtyFB_191, prime_oneHundredSixtyFB_377719540769508884552813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856027 : Nat.totient 189162701456451588401817856027 = 186448226602945071668715526176 := by
  rw [← show ((([(83, 1), (523, 1), (2423, 1), (170347, 1), (10557663666757063, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_83, prime_oneHundredSixtyFB_523, prime_oneHundredSixtyFB_2423, prime_oneHundredSixtyFB_170347, prime_oneHundredSixtyFB_10557663666757063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856028 : Nat.totient 189162701456451588401817856028 = 92945565620741490597277804800 := by
  rw [← show ((([(2, 2), (61, 1), (1091, 1), (710593009332886013740657, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_61, prime_oneHundredSixtyFB_1091, prime_oneHundredSixtyFB_710593009332886013740657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856029 : Nat.totient 189162701456451588401817856029 = 98799884051227600320853401600 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (107, 1), (2617, 1), (12401, 1), (199539395747394767, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_107, prime_oneHundredSixtyFB_2617, prime_oneHundredSixtyFB_12401, prime_oneHundredSixtyFB_199539395747394767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856030 : Nat.totient 189162701456451588401817856030 = 72969856641700927479509964480 := by
  rw [← show ((([(2, 1), (5, 1), (43, 2), (79, 1), (1233371, 1), (104997213222150383, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_43, prime_oneHundredSixtyFB_79, prime_oneHundredSixtyFB_1233371, prime_oneHundredSixtyFB_104997213222150383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856031 : Nat.totient 189162701456451588401817856031 = 178030037173595204086899379200 := by
  rw [← show ((([(17, 1), (35533, 1), (408211, 1), (767131837000485961, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_17, prime_oneHundredSixtyFB_35533, prime_oneHundredSixtyFB_408211, prime_oneHundredSixtyFB_767131837000485961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856032 : Nat.totient 189162701456451588401817856032 = 63054129976781833226307976704 := by
  rw [← show ((([(2, 5), (3, 2), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_607213, prime_oneHundredSixtyFB_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856033 : Nat.totient 189162701456451588401817856033 = 189162679444399887996078297648 := by
  rw [← show ((([(8593597, 1), (22012051700405730964789, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_8593597, prime_oneHundredSixtyFB_22012051700405730964789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856034 : Nat.totient 189162701456451588401817856034 = 90065751760763079404442393600 := by
  rw [← show ((([(2, 1), (31, 1), (73, 1), (443, 1), (19609, 1), (38011, 1), (126576327249287, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_31, prime_oneHundredSixtyFB_73, prime_oneHundredSixtyFB_443, prime_oneHundredSixtyFB_19609, prime_oneHundredSixtyFB_38011, prime_oneHundredSixtyFB_126576327249287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856035 : Nat.totient 189162701456451588401817856035 = 100886774110107513814302856544 := by
  rw [← show ((([(3, 1), (5, 1), (12610846763763439226787857069, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_12610846763763439226787857069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856036 : Nat.totient 189162701456451588401817856036 = 73083878434138948888731444480 := by
  rw [← show ((([(2, 2), (7, 1), (11, 1), (179, 1), (359, 1), (9557346059326019093897, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_179, prime_oneHundredSixtyFB_359, prime_oneHundredSixtyFB_9557346059326019093897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856037 : Nat.totient 189162701456451588401817856037 = 189111835867777542888110390448 := by
  rw [← show ((([(3719, 1), (193657207, 1), (426471607, 1), (615865027, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3719, prime_oneHundredSixtyFB_193657207, prime_oneHundredSixtyFB_426471607, prime_oneHundredSixtyFB_615865027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856038 : Nat.totient 189162701456451588401817856038 = 63035304080618872239461791200 := by
  rw [← show ((([(2, 1), (3, 1), (3331, 1), (289966661, 1), (32640857305682303, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_3331, prime_oneHundredSixtyFB_289966661, prime_oneHundredSixtyFB_32640857305682303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856039 : Nat.totient 189162701456451588401817856039 = 182639849654469814304463242400 := by
  rw [← show ((([(29, 1), (6612265111, 1), (986477654005303781, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_29, prime_oneHundredSixtyFB_6612265111, prime_oneHundredSixtyFB_986477654005303781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856040 : Nat.totient 189162701456451588401817856040 = 75655073266440591946121648640 := by
  rw [← show ((([(2, 3), (5, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_7561, prime_oneHundredSixtyFB_2416168199, prime_oneHundredSixtyFB_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856041 : Nat.totient 189162701456451588401817856041 = 122700130560340095321892512000 := by
  rw [← show ((([(3, 2), (37, 1), (1075232377, 1), (528310133400944501, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_37, prime_oneHundredSixtyFB_1075232377, prime_oneHundredSixtyFB_528310133400944501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856042 : Nat.totient 189162701456451588401817856042 = 87305862052381305006257721840 := by
  rw [← show ((([(2, 1), (13, 1), (551561071, 1), (13190721572073802727, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_551561071, prime_oneHundredSixtyFB_13190721572073802727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856043 : Nat.totient 189162701456451588401817856043 = 161051274106739223874222680000 := by
  rw [← show ((([(7, 1), (149, 1), (181364047417499125984485001, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_149, prime_oneHundredSixtyFB_181364047417499125984485001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856044 : Nat.totient 189162701456451588401817856044 = 63054233818817196133939285344 := by
  rw [← show ((([(2, 2), (3, 1), (15763558454704299033484821337, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_15763558454704299033484821337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856045 : Nat.totient 189162701456451588401817856045 = 143058415043399117408406897408 := by
  rw [← show ((([(5, 1), (19, 1), (467, 1), (19156283, 1), (158554247, 1), (1403802133, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_19, prime_oneHundredSixtyFB_467, prime_oneHundredSixtyFB_19156283, prime_oneHundredSixtyFB_158554247, prime_oneHundredSixtyFB_1403802133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856046 : Nat.totient 189162701456451588401817856046 = 92703550076090302752812502144 := by
  rw [← show ((([(2, 1), (109, 1), (139, 1), (277, 1), (150171907, 1), (150070644909607, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_109, prime_oneHundredSixtyFB_139, prime_oneHundredSixtyFB_277, prime_oneHundredSixtyFB_150171907, prime_oneHundredSixtyFB_150070644909607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856047 : Nat.totient 189162701456451588401817856047 = 114601584923320674187648581120 := by
  rw [← show ((([(3, 1), (11, 1), (2699, 1), (1639788413, 1), (1295182208051857, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_2699, prime_oneHundredSixtyFB_1639788413, prime_oneHundredSixtyFB_1295182208051857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856048 : Nat.totient 189162701456451588401817856048 = 88846882468641101506988482560 := by
  rw [← show ((([(2, 4), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_17, prime_oneHundredSixtyFB_521, prime_oneHundredSixtyFB_23096547757, prime_oneHundredSixtyFB_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856049 : Nat.totient 189162701456451588401817856049 = 180613597632509896025117900800 := by
  rw [← show ((([(23, 1), (641, 1), (4457, 1), (98669, 1), (29176035671262971, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_23, prime_oneHundredSixtyFB_641, prime_oneHundredSixtyFB_4457, prime_oneHundredSixtyFB_98669, prime_oneHundredSixtyFB_29176035671262971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856050 : Nat.totient 189162701456451588401817856050 = 43202197170579949028720455680 := by
  rw [← show ((([(2, 1), (3, 4), (5, 2), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_1277, prime_oneHundredSixtyFB_38153, prime_oneHundredSixtyFB_45994279, prime_oneHundredSixtyFB_2977549837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856051 : Nat.totient 189162701456451588401817856051 = 189160025395769193455244839592 := by
  rw [← show ((([(70687, 1), (2676060682394946572945773, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_70687, prime_oneHundredSixtyFB_2676060682394946572945773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856052 : Nat.totient 189162701456451588401817856052 = 94581350728225794200908928024 := by
  rw [← show ((([(2, 2), (47290675364112897100454464013, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_47290675364112897100454464013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856053 : Nat.totient 189162701456451588401817856053 = 126104984844195257401070028608 := by
  rw [← show ((([(3, 1), (36209, 1), (1741396719567433404234839, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_36209, prime_oneHundredSixtyFB_1741396719567433404234839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856054 : Nat.totient 189162701456451588401817856054 = 94581350728225794200908928026 := by
  rw [← show ((([(2, 1), (94581350728225794200908928027, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_94581350728225794200908928027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856055 : Nat.totient 189162701456451588401817856055 = 136520380515702528641153249280 := by
  rw [← show ((([(5, 1), (13, 1), (47, 1), (827, 1), (4327, 1), (14642821, 1), (1181699726089, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_47, prime_oneHundredSixtyFB_827, prime_oneHundredSixtyFB_4327, prime_oneHundredSixtyFB_14642821, prime_oneHundredSixtyFB_1181699726089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856056 : Nat.totient 189162701456451588401817856056 = 63054228255217002438515602400 := by
  rw [← show ((([(2, 3), (3, 1), (11333351, 1), (695450024211916627019, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_11333351, prime_oneHundredSixtyFB_695450024211916627019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856057 : Nat.totient 189162701456451588401817856057 = 161106013556879469400661084928 := by
  rw [← show ((([(7, 2), (157, 1), (227093, 1), (108276953428340218793, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_157, prime_oneHundredSixtyFB_227093, prime_oneHundredSixtyFB_108276953428340218793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856058 : Nat.totient 189162701456451588401817856058 = 85591072393018653549858000000 := by
  rw [← show ((([(2, 1), (11, 1), (223, 1), (13751, 1), (489911, 1), (5723431519180313, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_223, prime_oneHundredSixtyFB_13751, prime_oneHundredSixtyFB_489911, prime_oneHundredSixtyFB_5723431519180313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856059 : Nat.totient 189162701456451588401817856059 = 126108016530088997890451976192 := by
  rw [← show ((([(3, 2), (279553, 1), (75184590899062904152867, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_279553, prime_oneHundredSixtyFB_75184590899062904152867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856060 : Nat.totient 189162701456451588401817856060 = 75564307122278168809074600000 := by
  rw [← show ((([(2, 2), (5, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_751, prime_oneHundredSixtyFB_3594403, prime_oneHundredSixtyFB_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856061 : Nat.totient 189162701456451588401817856061 = 189162540332671471647867304800 := by
  rw [← show ((([(1174021, 1), (161123780116753949377241, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_1174021, prime_oneHundredSixtyFB_161123780116753949377241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856062 : Nat.totient 189162701456451588401817856062 = 62705867886116548641486581760 := by
  rw [← show ((([(2, 1), (3, 1), (181, 1), (174182966350323746226351617, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_181, prime_oneHundredSixtyFB_174182966350323746226351617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856063 : Nat.totient 189162701456451588401817856063 = 186227525173620089643616788480 := by
  rw [← show ((([(67, 1), (2953, 1), (3821, 1), (250218963210430951553, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_67, prime_oneHundredSixtyFB_2953, prime_oneHundredSixtyFB_3821, prime_oneHundredSixtyFB_250218963210430951553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856064 : Nat.totient 189162701456451588401817856064 = 74740914661269450880796590080 := by
  rw [← show ((([(2, 6), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_19, prime_oneHundredSixtyFB_41, prime_oneHundredSixtyFB_397, prime_oneHundredSixtyFB_13617913, prime_oneHundredSixtyFB_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856065 : Nat.totient 189162701456451588401817856065 = 91884362800122465018035466240 := by
  rw [← show ((([(3, 1), (5, 1), (17, 1), (31, 1), (26947, 1), (60887, 1), (14584738097576557, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_17, prime_oneHundredSixtyFB_31, prime_oneHundredSixtyFB_26947, prime_oneHundredSixtyFB_60887, prime_oneHundredSixtyFB_14584738097576557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856066 : Nat.totient 189162701456451588401817856066 = 94581350728225794200908928032 := by
  rw [← show ((([(2, 1), (94581350728225794200908928033, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_94581350728225794200908928033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856067 : Nat.totient 189162701456451588401817856067 = 189161393883187081281407377200 := by
  rw [← show ((([(144667, 1), (1307573264507120410334201, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_144667, prime_oneHundredSixtyFB_1307573264507120410334201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856068 : Nat.totient 189162701456451588401817856068 = 56196876263717655423381295872 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (29, 1), (100076147, 1), (139271123883117227, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_29, prime_oneHundredSixtyFB_100076147, prime_oneHundredSixtyFB_139271123883117227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856069 : Nat.totient 189162701456451588401817856069 = 170444268408065791641219627840 := by
  rw [← show ((([(11, 1), (113, 1), (152182382507201599679660383, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_113, prime_oneHundredSixtyFB_152182382507201599679660383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856070 : Nat.totient 189162701456451588401817856070 = 75659261534623811501974438944 := by
  rw [← show ((([(2, 1), (5, 1), (13003, 1), (1454761989205964688162869, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_13003, prime_oneHundredSixtyFB_1454761989205964688162869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856071 : Nat.totient 189162701456451588401817856071 = 106975743387290963868266864640 := by
  rw [← show ((([(3, 1), (7, 1), (97, 1), (37309, 1), (110589257, 1), (22507016516591, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_97, prime_oneHundredSixtyFB_37309, prime_oneHundredSixtyFB_110589257, prime_oneHundredSixtyFB_22507016516591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856072 : Nat.totient 189162701456451588401817856072 = 90070153523037250058979712768 := by
  rw [← show ((([(2, 3), (23, 1), (227, 1), (235397, 1), (2276699, 1), (8450556055043, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_23, prime_oneHundredSixtyFB_227, prime_oneHundredSixtyFB_235397, prime_oneHundredSixtyFB_2276699, prime_oneHundredSixtyFB_8450556055043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856073 : Nat.totient 189162701456451588401817856073 = 184763568857657911114100184000 := by
  rw [← show ((([(43, 1), (27238512011, 1), (161504144948665201, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_43, prime_oneHundredSixtyFB_27238512011, prime_oneHundredSixtyFB_161504144948665201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856074 : Nat.totient 189162701456451588401817856074 = 61884862265498253265812380160 := by
  rw [← show ((([(2, 1), (3, 1), (59, 1), (617, 1), (361787, 1), (2823221, 1), (847909006459, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_59, prime_oneHundredSixtyFB_617, prime_oneHundredSixtyFB_361787, prime_oneHundredSixtyFB_2823221, prime_oneHundredSixtyFB_847909006459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856075 : Nat.totient 189162701456451588401817856075 = 151330161165161270721454284840 := by
  rw [← show ((([(5, 2), (7566508058258063536072714243, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_7566508058258063536072714243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856076 : Nat.totient 189162701456451588401817856076 = 94580513702900093290316377392 := by
  rw [← show ((([(2, 2), (112997, 1), (418512662850455296162327, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_112997, prime_oneHundredSixtyFB_418512662850455296162327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856077 : Nat.totient 189162701456451588401817856077 = 126108467637583974788234329200 := by
  rw [← show ((([(3, 3), (2503522305341, 1), (2798467569041411, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_2503522305341, prime_oneHundredSixtyFB_2798467569041411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856078 : Nat.totient 189162701456451588401817856078 = 77386007542308038126133235200 := by
  rw [← show ((([(2, 1), (7, 1), (37, 1), (53, 1), (17791, 1), (3616147, 1), (107098513236541, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_37, prime_oneHundredSixtyFB_53, prime_oneHundredSixtyFB_17791, prime_oneHundredSixtyFB_3616147, prime_oneHundredSixtyFB_107098513236541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856079 : Nat.totient 189162701456451588401817856079 = 189162701453406158503579082280 := by
  rw [← show ((([(62113629811, 1), (3045429836125143989, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_62113629811, prime_oneHundredSixtyFB_3045429836125143989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856080 : Nat.totient 189162701456451588401817856080 = 45757496639721319570937856000 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_461, prime_oneHundredSixtyFB_69997, prime_oneHundredSixtyFB_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856081 : Nat.totient 189162701456451588401817856081 = 174610892008864520265631060800 := by
  rw [← show ((([(13, 1), (210031, 1), (166169831, 1), (416923693962317, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_210031, prime_oneHundredSixtyFB_166169831, prime_oneHundredSixtyFB_416923693962317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856082 : Nat.totient 189162701456451588401817856082 = 88914120358031109318458971648 := by
  rw [← show ((([(2, 1), (17, 1), (863, 1), (188249, 1), (34246257432295613279, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_17, prime_oneHundredSixtyFB_863, prime_oneHundredSixtyFB_188249, prime_oneHundredSixtyFB_34246257432295613279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856083 : Nat.totient 189162701456451588401817856083 = 119471096362471755375914779680 := by
  rw [← show ((([(3, 1), (19, 1), (1430711, 1), (2319576689632570840429, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_19, prime_oneHundredSixtyFB_1430711, prime_oneHundredSixtyFB_2319576689632570840429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856084 : Nat.totient 189162701456451588401817856084 = 94581350728224136475863688984 := by
  rw [← show ((([(2, 2), (61638694796963, 1), (767223827822567, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_61638694796963, prime_oneHundredSixtyFB_767223827822567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856085 : Nat.totient 189162701456451588401817856085 = 129445217113082432290654141440 := by
  rw [← show ((([(5, 1), (7, 1), (487, 1), (91568473, 1), (121197184259488681, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_487, prime_oneHundredSixtyFB_91568473, prime_oneHundredSixtyFB_121197184259488681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856086 : Nat.totient 189162701456451588401817856086 = 63038231054693138835942893568 := by
  rw [← show ((([(2, 1), (3, 2), (3967, 1), (587107, 1), (89785217, 1), (50254933999, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_3967, prime_oneHundredSixtyFB_587107, prime_oneHundredSixtyFB_89785217, prime_oneHundredSixtyFB_50254933999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856087 : Nat.totient 189162701456451588401817856087 = 188888949355935739503985991640 := by
  rw [← show ((([(691, 1), (273752100515848897831863757, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_691, prime_oneHundredSixtyFB_273752100515848897831863757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856088 : Nat.totient 189162701456451588401817856088 = 94581350728225794200908928040 := by
  rw [← show ((([(2, 3), (23645337682056448550227232011, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_23645337682056448550227232011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856089 : Nat.totient 189162701456451588401817856089 = 124041115708977220517781053760 := by
  rw [← show ((([(3, 1), (61, 1), (724221389597, 1), (1427292785177339, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_61, prime_oneHundredSixtyFB_724221389597, prime_oneHundredSixtyFB_1427292785177339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856090 : Nat.totient 189162701456451588401817856090 = 74283865382498544278615800320 := by
  rw [← show ((([(2, 1), (5, 1), (71, 1), (239, 1), (22307, 1), (1536649, 1), (32520964175027, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_71, prime_oneHundredSixtyFB_239, prime_oneHundredSixtyFB_22307, prime_oneHundredSixtyFB_1536649, prime_oneHundredSixtyFB_32520964175027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856091 : Nat.totient 189162701456451588401817856091 = 171965634344335574356720809120 := by
  rw [← show ((([(11, 2), (375563, 1), (4162625474848011401017, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_11, prime_oneHundredSixtyFB_375563, prime_oneHundredSixtyFB_4162625474848011401017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856092 : Nat.totient 189162701456451588401817856092 = 54046486054446707807682661440 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (711437231, 1), (3165334654942473973, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_711437231, prime_oneHundredSixtyFB_3165334654942473973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856093 : Nat.totient 189162701456451588401817856093 = 189162127616614639675350140160 := by
  rw [← show ((([(350521, 1), (5534569, 1), (97507418655314557, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_350521, prime_oneHundredSixtyFB_5534569, prime_oneHundredSixtyFB_97507418655314557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856094 : Nat.totient 189162701456451588401817856094 = 87055702147029075729115200480 := by
  rw [← show ((([(2, 1), (13, 1), (349, 1), (20846671970074012387240231, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_13, prime_oneHundredSixtyFB_349, prime_oneHundredSixtyFB_20846671970074012387240231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856095 : Nat.totient 189162701456451588401817856095 = 96500392505835673519610519040 := by
  rw [← show ((([(3, 2), (5, 1), (23, 1), (796052281, 1), (229590316476973157, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_23, prime_oneHundredSixtyFB_796052281, prime_oneHundredSixtyFB_229590316476973157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856096 : Nat.totient 189162701456451588401817856096 = 91530313982316886477952471040 := by
  rw [← show ((([(2, 5), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_31, prime_oneHundredSixtyFB_3599009, prime_oneHundredSixtyFB_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856097 : Nat.totient 189162701456451588401817856097 = 182015090041666526265762970752 := by
  rw [← show ((([(29, 1), (563, 1), (607, 1), (19087120873294101673673, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_29, prime_oneHundredSixtyFB_563, prime_oneHundredSixtyFB_607, prime_oneHundredSixtyFB_19087120873294101673673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856098 : Nat.totient 189162701456451588401817856098 = 63042193639504322299512929088 := by
  rw [← show ((([(2, 1), (3, 1), (5237, 1), (1782268003, 1), (3377759102642053, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_5237, prime_oneHundredSixtyFB_1782268003, prime_oneHundredSixtyFB_3377759102642053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856099 : Nat.totient 189162701456451588401817856099 = 152601841661267252122747840512 := by
  rw [← show ((([(7, 1), (17, 1), (105211543, 1), (3188827619, 1), (4737989713, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_7, prime_oneHundredSixtyFB_17, prime_oneHundredSixtyFB_105211543, prime_oneHundredSixtyFB_3188827619, prime_oneHundredSixtyFB_4737989713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856100 : Nat.totient 189162701456451588401817856100 = 75323912657956128479797862400 := by
  rw [← show ((([(2, 2), (5, 2), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_2, prime_oneHundredSixtyFB_5, prime_oneHundredSixtyFB_271, prime_oneHundredSixtyFB_1217, prime_oneHundredSixtyFB_4440187, prime_oneHundredSixtyFB_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFB_189162701456451588401817856101 : Nat.totient 189162701456451588401817856101 = 126107372139737089104113126400 := by
  rw [← show ((([(3, 1), (123373, 1), (1732967, 1), (292809137, 1), (1007208101, 1)] : List FactorBlock).map factorBlockValue).prod) = 189162701456451588401817856101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFB_3, prime_oneHundredSixtyFB_123373, prime_oneHundredSixtyFB_1732967, prime_oneHundredSixtyFB_292809137, prime_oneHundredSixtyFB_1007208101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyFB : certifiedKill 1 189162701456451588401817855999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyFB_189162701456451588401817856000, phi_oneHundredSixtyFB_189162701456451588401817856001, phi_oneHundredSixtyFB_189162701456451588401817856002,
    phi_oneHundredSixtyFB_189162701456451588401817856003, phi_oneHundredSixtyFB_189162701456451588401817856004, phi_oneHundredSixtyFB_189162701456451588401817856005,
    phi_oneHundredSixtyFB_189162701456451588401817856006, phi_oneHundredSixtyFB_189162701456451588401817856007, phi_oneHundredSixtyFB_189162701456451588401817856008,
    phi_oneHundredSixtyFB_189162701456451588401817856009, phi_oneHundredSixtyFB_189162701456451588401817856010, phi_oneHundredSixtyFB_189162701456451588401817856011,
    phi_oneHundredSixtyFB_189162701456451588401817856012, phi_oneHundredSixtyFB_189162701456451588401817856013, phi_oneHundredSixtyFB_189162701456451588401817856014,
    phi_oneHundredSixtyFB_189162701456451588401817856015, phi_oneHundredSixtyFB_189162701456451588401817856016, phi_oneHundredSixtyFB_189162701456451588401817856017,
    phi_oneHundredSixtyFB_189162701456451588401817856018, phi_oneHundredSixtyFB_189162701456451588401817856019, phi_oneHundredSixtyFB_189162701456451588401817856020,
    phi_oneHundredSixtyFB_189162701456451588401817856021, phi_oneHundredSixtyFB_189162701456451588401817856022, phi_oneHundredSixtyFB_189162701456451588401817856023,
    phi_oneHundredSixtyFB_189162701456451588401817856024, phi_oneHundredSixtyFB_189162701456451588401817856025, phi_oneHundredSixtyFB_189162701456451588401817856026,
    phi_oneHundredSixtyFB_189162701456451588401817856027, phi_oneHundredSixtyFB_189162701456451588401817856028, phi_oneHundredSixtyFB_189162701456451588401817856029,
    phi_oneHundredSixtyFB_189162701456451588401817856030, phi_oneHundredSixtyFB_189162701456451588401817856031, phi_oneHundredSixtyFB_189162701456451588401817856032,
    phi_oneHundredSixtyFB_189162701456451588401817856033, phi_oneHundredSixtyFB_189162701456451588401817856034, phi_oneHundredSixtyFB_189162701456451588401817856035,
    phi_oneHundredSixtyFB_189162701456451588401817856036, phi_oneHundredSixtyFB_189162701456451588401817856037, phi_oneHundredSixtyFB_189162701456451588401817856038,
    phi_oneHundredSixtyFB_189162701456451588401817856039, phi_oneHundredSixtyFB_189162701456451588401817856040, phi_oneHundredSixtyFB_189162701456451588401817856041,
    phi_oneHundredSixtyFB_189162701456451588401817856042, phi_oneHundredSixtyFB_189162701456451588401817856043, phi_oneHundredSixtyFB_189162701456451588401817856044,
    phi_oneHundredSixtyFB_189162701456451588401817856045, phi_oneHundredSixtyFB_189162701456451588401817856046, phi_oneHundredSixtyFB_189162701456451588401817856047,
    phi_oneHundredSixtyFB_189162701456451588401817856048, phi_oneHundredSixtyFB_189162701456451588401817856049, phi_oneHundredSixtyFB_189162701456451588401817856050,
    phi_oneHundredSixtyFB_189162701456451588401817856051, phi_oneHundredSixtyFB_189162701456451588401817856052, phi_oneHundredSixtyFB_189162701456451588401817856053,
    phi_oneHundredSixtyFB_189162701456451588401817856054, phi_oneHundredSixtyFB_189162701456451588401817856055, phi_oneHundredSixtyFB_189162701456451588401817856056,
    phi_oneHundredSixtyFB_189162701456451588401817856057, phi_oneHundredSixtyFB_189162701456451588401817856058, phi_oneHundredSixtyFB_189162701456451588401817856059,
    phi_oneHundredSixtyFB_189162701456451588401817856060, phi_oneHundredSixtyFB_189162701456451588401817856061, phi_oneHundredSixtyFB_189162701456451588401817856062,
    phi_oneHundredSixtyFB_189162701456451588401817856063, phi_oneHundredSixtyFB_189162701456451588401817856064, phi_oneHundredSixtyFB_189162701456451588401817856065,
    phi_oneHundredSixtyFB_189162701456451588401817856066, phi_oneHundredSixtyFB_189162701456451588401817856067, phi_oneHundredSixtyFB_189162701456451588401817856068,
    phi_oneHundredSixtyFB_189162701456451588401817856069, phi_oneHundredSixtyFB_189162701456451588401817856070, phi_oneHundredSixtyFB_189162701456451588401817856071,
    phi_oneHundredSixtyFB_189162701456451588401817856072, phi_oneHundredSixtyFB_189162701456451588401817856073, phi_oneHundredSixtyFB_189162701456451588401817856074,
    phi_oneHundredSixtyFB_189162701456451588401817856075, phi_oneHundredSixtyFB_189162701456451588401817856076, phi_oneHundredSixtyFB_189162701456451588401817856077,
    phi_oneHundredSixtyFB_189162701456451588401817856078, phi_oneHundredSixtyFB_189162701456451588401817856079, phi_oneHundredSixtyFB_189162701456451588401817856080,
    phi_oneHundredSixtyFB_189162701456451588401817856081, phi_oneHundredSixtyFB_189162701456451588401817856082, phi_oneHundredSixtyFB_189162701456451588401817856083,
    phi_oneHundredSixtyFB_189162701456451588401817856084, phi_oneHundredSixtyFB_189162701456451588401817856085, phi_oneHundredSixtyFB_189162701456451588401817856086,
    phi_oneHundredSixtyFB_189162701456451588401817856087, phi_oneHundredSixtyFB_189162701456451588401817856088, phi_oneHundredSixtyFB_189162701456451588401817856089,
    phi_oneHundredSixtyFB_189162701456451588401817856090, phi_oneHundredSixtyFB_189162701456451588401817856091, phi_oneHundredSixtyFB_189162701456451588401817856092,
    phi_oneHundredSixtyFB_189162701456451588401817856093, phi_oneHundredSixtyFB_189162701456451588401817856094, phi_oneHundredSixtyFB_189162701456451588401817856095,
    phi_oneHundredSixtyFB_189162701456451588401817856096, phi_oneHundredSixtyFB_189162701456451588401817856097, phi_oneHundredSixtyFB_189162701456451588401817856098,
    phi_oneHundredSixtyFB_189162701456451588401817856099, phi_oneHundredSixtyFB_189162701456451588401817856100, phi_oneHundredSixtyFB_189162701456451588401817856101
    ]

end TotientTailPeriodKiller
end Erdos249257

