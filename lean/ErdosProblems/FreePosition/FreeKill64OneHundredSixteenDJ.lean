import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixteenDJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixteenDJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixteenDJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixteenDJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixteenDJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixteenDJFastPow a n * oneHundredSixteenDJFastPow a n * a else oneHundredSixteenDJFastPow a n * oneHundredSixteenDJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixteenDJ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixteenDJ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixteenDJ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixteenDJ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixteenDJ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixteenDJ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixteenDJ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixteenDJ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixteenDJ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixteenDJ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixteenDJ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixteenDJ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixteenDJ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixteenDJ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixteenDJ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixteenDJ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixteenDJ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixteenDJ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixteenDJ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixteenDJ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixteenDJ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixteenDJ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixteenDJ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixteenDJ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixteenDJ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixteenDJ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixteenDJ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixteenDJ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixteenDJ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixteenDJ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixteenDJ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixteenDJ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixteenDJ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixteenDJ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixteenDJ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixteenDJ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixteenDJ_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixteenDJ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixteenDJ_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixteenDJ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixteenDJ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixteenDJ_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSixteenDJ_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixteenDJ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixteenDJ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSixteenDJ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixteenDJ_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixteenDJ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixteenDJ_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixteenDJ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixteenDJ_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSixteenDJ_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixteenDJ_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSixteenDJ_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixteenDJ_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixteenDJ_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixteenDJ_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixteenDJ_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSixteenDJ_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSixteenDJ_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixteenDJ_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredSixteenDJ_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredSixteenDJ_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSixteenDJ_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredSixteenDJ_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSixteenDJ_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixteenDJ_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredSixteenDJ_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSixteenDJ_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredSixteenDJ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixteenDJ_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSixteenDJ_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSixteenDJ_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredSixteenDJ_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredSixteenDJ_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixteenDJ_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixteenDJ_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSixteenDJ_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredSixteenDJ_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredSixteenDJ_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixteenDJ_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredSixteenDJ_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSixteenDJ_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredSixteenDJ_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredSixteenDJ_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixteenDJ_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredSixteenDJ_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSixteenDJ_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredSixteenDJ_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredSixteenDJ_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredSixteenDJ_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSixteenDJ_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixteenDJ_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredSixteenDJ_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredSixteenDJ_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredSixteenDJ_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredSixteenDJ_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredSixteenDJ_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredSixteenDJ_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredSixteenDJ_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredSixteenDJ_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredSixteenDJ_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredSixteenDJ_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredSixteenDJ_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredSixteenDJ_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredSixteenDJ_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredSixteenDJ_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredSixteenDJ_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredSixteenDJ_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredSixteenDJ_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredSixteenDJ_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredSixteenDJ_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredSixteenDJ_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredSixteenDJ_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredSixteenDJ_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredSixteenDJ_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredSixteenDJ_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredSixteenDJ_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredSixteenDJ_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredSixteenDJ_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredSixteenDJ_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredSixteenDJ_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredSixteenDJ_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_oneHundredSixteenDJ_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredSixteenDJ_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredSixteenDJ_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredSixteenDJ_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_oneHundredSixteenDJ_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_oneHundredSixteenDJ_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredSixteenDJ_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredSixteenDJ_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredSixteenDJ_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredSixteenDJ_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredSixteenDJ_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_oneHundredSixteenDJ_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_oneHundredSixteenDJ_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredSixteenDJ_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_oneHundredSixteenDJ_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_oneHundredSixteenDJ_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredSixteenDJ_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_oneHundredSixteenDJ_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredSixteenDJ_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredSixteenDJ_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredSixteenDJ_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_oneHundredSixteenDJ_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredSixteenDJ_3329 : Nat.Prime 3329 := by norm_num

private theorem prime_oneHundredSixteenDJ_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_oneHundredSixteenDJ_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_oneHundredSixteenDJ_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredSixteenDJ_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_oneHundredSixteenDJ_4591 : Nat.Prime 4591 := by norm_num

private theorem prime_oneHundredSixteenDJ_4597 : Nat.Prime 4597 := by norm_num

private theorem prime_oneHundredSixteenDJ_4817 : Nat.Prime 4817 := by norm_num

private theorem prime_oneHundredSixteenDJ_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_oneHundredSixteenDJ_4967 : Nat.Prime 4967 := by norm_num

private theorem prime_oneHundredSixteenDJ_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_oneHundredSixteenDJ_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_oneHundredSixteenDJ_6089 : Nat.Prime 6089 := by norm_num

private theorem prime_oneHundredSixteenDJ_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredSixteenDJ_6607 : Nat.Prime 6607 := by norm_num

private theorem prime_oneHundredSixteenDJ_7351 : Nat.Prime 7351 := by norm_num

private theorem prime_oneHundredSixteenDJ_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredSixteenDJ_7723 : Nat.Prime 7723 := by norm_num

private theorem prime_oneHundredSixteenDJ_7963 : Nat.Prime 7963 := by norm_num

private theorem prime_oneHundredSixteenDJ_8179 : Nat.Prime 8179 := by norm_num

private theorem prime_oneHundredSixteenDJ_8191 : Nat.Prime 8191 := by norm_num

private theorem prime_oneHundredSixteenDJ_8231 : Nat.Prime 8231 := by norm_num

private theorem prime_oneHundredSixteenDJ_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredSixteenDJ_8543 : Nat.Prime 8543 := by norm_num

private theorem prime_oneHundredSixteenDJ_8761 : Nat.Prime 8761 := by norm_num

private theorem prime_oneHundredSixteenDJ_8821 : Nat.Prime 8821 := by norm_num

private theorem prime_oneHundredSixteenDJ_9277 : Nat.Prime 9277 := by norm_num

private theorem prime_oneHundredSixteenDJ_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_oneHundredSixteenDJ_9521 : Nat.Prime 9521 := by norm_num

private theorem prime_oneHundredSixteenDJ_9857 : Nat.Prime 9857 := by norm_num

private theorem prime_oneHundredSixteenDJ_9949 : Nat.Prime 9949 := by norm_num

private theorem prime_oneHundredSixteenDJ_10009 : Nat.Prime 10009 := by norm_num

private theorem prime_oneHundredSixteenDJ_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredSixteenDJ_11351 : Nat.Prime 11351 := by norm_num

private theorem prime_oneHundredSixteenDJ_11807 : Nat.Prime 11807 := by norm_num

private theorem prime_oneHundredSixteenDJ_12011 : Nat.Prime 12011 := by norm_num

private theorem prime_oneHundredSixteenDJ_12043 : Nat.Prime 12043 := by norm_num

private theorem prime_oneHundredSixteenDJ_12577 : Nat.Prime 12577 := by norm_num

private theorem prime_oneHundredSixteenDJ_13597 : Nat.Prime 13597 := by norm_num

private theorem prime_oneHundredSixteenDJ_14009 : Nat.Prime 14009 := by norm_num

private theorem prime_oneHundredSixteenDJ_14249 : Nat.Prime 14249 := by norm_num

private theorem prime_oneHundredSixteenDJ_14461 : Nat.Prime 14461 := by norm_num

private theorem prime_oneHundredSixteenDJ_14519 : Nat.Prime 14519 := by norm_num

private theorem prime_oneHundredSixteenDJ_14891 : Nat.Prime 14891 := by norm_num

private theorem prime_oneHundredSixteenDJ_15187 : Nat.Prime 15187 := by norm_num

private theorem prime_oneHundredSixteenDJ_15233 : Nat.Prime 15233 := by norm_num

private theorem prime_oneHundredSixteenDJ_15401 : Nat.Prime 15401 := by norm_num

private theorem prime_oneHundredSixteenDJ_15607 : Nat.Prime 15607 := by norm_num

private theorem prime_oneHundredSixteenDJ_15913 : Nat.Prime 15913 := by norm_num

private theorem prime_oneHundredSixteenDJ_15919 : Nat.Prime 15919 := by norm_num

private theorem prime_oneHundredSixteenDJ_15937 : Nat.Prime 15937 := by norm_num

private theorem prime_oneHundredSixteenDJ_16061 : Nat.Prime 16061 := by norm_num

private theorem prime_oneHundredSixteenDJ_16561 : Nat.Prime 16561 := by norm_num

private theorem prime_oneHundredSixteenDJ_16699 : Nat.Prime 16699 := by norm_num

private theorem prime_oneHundredSixteenDJ_16763 : Nat.Prime 16763 := by norm_num

private theorem prime_oneHundredSixteenDJ_17183 : Nat.Prime 17183 := by norm_num

private theorem prime_oneHundredSixteenDJ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixteenDJ_17419 : Nat.Prime 17419 := by norm_num

private theorem prime_oneHundredSixteenDJ_17573 : Nat.Prime 17573 := by norm_num

private theorem prime_oneHundredSixteenDJ_18587 : Nat.Prime 18587 := by norm_num

private theorem prime_oneHundredSixteenDJ_19381 : Nat.Prime 19381 := by norm_num

private theorem prime_oneHundredSixteenDJ_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredSixteenDJ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixteenDJ_22469 : Nat.Prime 22469 := by norm_num

private theorem prime_oneHundredSixteenDJ_23063 : Nat.Prime 23063 := by norm_num

private theorem prime_oneHundredSixteenDJ_24359 : Nat.Prime 24359 := by norm_num

private theorem prime_oneHundredSixteenDJ_24977 : Nat.Prime 24977 := by norm_num

private theorem prime_oneHundredSixteenDJ_25349 : Nat.Prime 25349 := by norm_num

private theorem prime_oneHundredSixteenDJ_26959 : Nat.Prime 26959 := by norm_num

private theorem prime_oneHundredSixteenDJ_27947 : Nat.Prime 27947 := by norm_num

private theorem prime_oneHundredSixteenDJ_29243 : Nat.Prime 29243 := by norm_num

private theorem prime_oneHundredSixteenDJ_30313 : Nat.Prime 30313 := by norm_num

private theorem prime_oneHundredSixteenDJ_31379 : Nat.Prime 31379 := by norm_num

private theorem prime_oneHundredSixteenDJ_32537 : Nat.Prime 32537 := by norm_num

private theorem prime_oneHundredSixteenDJ_34039 : Nat.Prime 34039 := by norm_num

private theorem prime_oneHundredSixteenDJ_34327 : Nat.Prime 34327 := by norm_num

private theorem prime_oneHundredSixteenDJ_34649 : Nat.Prime 34649 := by norm_num

private theorem prime_oneHundredSixteenDJ_35461 : Nat.Prime 35461 := by norm_num

private theorem prime_oneHundredSixteenDJ_36901 : Nat.Prime 36901 := by norm_num

private theorem prime_oneHundredSixteenDJ_38047 : Nat.Prime 38047 := by norm_num

private theorem prime_oneHundredSixteenDJ_39847 : Nat.Prime 39847 := by norm_num

private theorem prime_oneHundredSixteenDJ_40351 : Nat.Prime 40351 := by norm_num

private theorem prime_oneHundredSixteenDJ_41257 : Nat.Prime 41257 := by norm_num

private theorem prime_oneHundredSixteenDJ_41479 : Nat.Prime 41479 := by norm_num

private theorem prime_oneHundredSixteenDJ_43411 : Nat.Prime 43411 := by norm_num

private theorem prime_oneHundredSixteenDJ_46133 : Nat.Prime 46133 := by norm_num

private theorem prime_oneHundredSixteenDJ_46439 : Nat.Prime 46439 := by norm_num

private theorem prime_oneHundredSixteenDJ_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredSixteenDJ_48353 : Nat.Prime 48353 := by norm_num

private theorem prime_oneHundredSixteenDJ_50111 : Nat.Prime 50111 := by norm_num

private theorem prime_oneHundredSixteenDJ_52147 : Nat.Prime 52147 := by norm_num

private theorem prime_oneHundredSixteenDJ_53147 : Nat.Prime 53147 := by norm_num

private theorem prime_oneHundredSixteenDJ_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredSixteenDJ_59377 : Nat.Prime 59377 := by norm_num

private theorem prime_oneHundredSixteenDJ_61471 : Nat.Prime 61471 := by norm_num

private theorem prime_oneHundredSixteenDJ_63577 : Nat.Prime 63577 := by norm_num

private theorem prime_oneHundredSixteenDJ_65843 : Nat.Prime 65843 := by norm_num

private theorem prime_oneHundredSixteenDJ_69847 : Nat.Prime 69847 := by norm_num

private theorem prime_oneHundredSixteenDJ_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredSixteenDJ_70099 : Nat.Prime 70099 := by norm_num

private theorem prime_oneHundredSixteenDJ_72251 : Nat.Prime 72251 := by norm_num

private theorem prime_oneHundredSixteenDJ_73883 : Nat.Prime 73883 := by norm_num

private theorem prime_oneHundredSixteenDJ_73951 : Nat.Prime 73951 := by norm_num

private theorem prime_oneHundredSixteenDJ_75041 : Nat.Prime 75041 := by norm_num

private theorem prime_oneHundredSixteenDJ_79613 : Nat.Prime 79613 := by norm_num

private theorem prime_oneHundredSixteenDJ_83761 : Nat.Prime 83761 := by norm_num

private theorem prime_oneHundredSixteenDJ_84377 : Nat.Prime 84377 := by norm_num

private theorem prime_oneHundredSixteenDJ_85661 : Nat.Prime 85661 := by norm_num

private theorem prime_oneHundredSixteenDJ_86587 : Nat.Prime 86587 := by norm_num

private theorem prime_oneHundredSixteenDJ_88321 : Nat.Prime 88321 := by norm_num

private theorem prime_oneHundredSixteenDJ_89627 : Nat.Prime 89627 := by norm_num

private theorem prime_oneHundredSixteenDJ_91159 : Nat.Prime 91159 := by norm_num

private theorem prime_oneHundredSixteenDJ_92369 : Nat.Prime 92369 := by norm_num

private theorem prime_oneHundredSixteenDJ_92789 : Nat.Prime 92789 := by norm_num

private theorem prime_oneHundredSixteenDJ_99409 : Nat.Prime 99409 := by norm_num

private theorem prime_oneHundredSixteenDJ_101221 : Nat.Prime 101221 := by norm_num

private theorem prime_oneHundredSixteenDJ_101929 : Nat.Prime 101929 := by norm_num

private theorem prime_oneHundredSixteenDJ_104779 : Nat.Prime 104779 := by norm_num

private theorem prime_oneHundredSixteenDJ_105653 : Nat.Prime 105653 := by norm_num

private theorem prime_oneHundredSixteenDJ_106963 : Nat.Prime 106963 := by norm_num

private theorem prime_oneHundredSixteenDJ_115837 : Nat.Prime 115837 := by norm_num

private theorem prime_oneHundredSixteenDJ_116047 : Nat.Prime 116047 := by norm_num

private theorem prime_oneHundredSixteenDJ_123217 : Nat.Prime 123217 := by norm_num

private theorem prime_oneHundredSixteenDJ_123551 : Nat.Prime 123551 := by norm_num

private theorem prime_oneHundredSixteenDJ_128213 : Nat.Prime 128213 := by norm_num

private theorem prime_oneHundredSixteenDJ_132421 : Nat.Prime 132421 := by norm_num

private theorem prime_oneHundredSixteenDJ_133073 : Nat.Prime 133073 := by norm_num

private theorem prime_oneHundredSixteenDJ_134327 : Nat.Prime 134327 := by norm_num

private theorem prime_oneHundredSixteenDJ_139921 : Nat.Prime 139921 := by norm_num

private theorem prime_oneHundredSixteenDJ_150343 : Nat.Prime 150343 := by norm_num

private theorem prime_oneHundredSixteenDJ_150889 : Nat.Prime 150889 := by norm_num

private theorem prime_oneHundredSixteenDJ_158761 : Nat.Prime 158761 := by norm_num

private theorem prime_oneHundredSixteenDJ_160403 : Nat.Prime 160403 := by norm_num

private theorem prime_oneHundredSixteenDJ_161387 : Nat.Prime 161387 := by norm_num

private theorem prime_oneHundredSixteenDJ_165437 : Nat.Prime 165437 := by norm_num

private theorem prime_oneHundredSixteenDJ_169249 : Nat.Prime 169249 := by norm_num

private theorem prime_oneHundredSixteenDJ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixteenDJ_179173 : Nat.Prime 179173 := by norm_num

private theorem prime_oneHundredSixteenDJ_181777 : Nat.Prime 181777 := by norm_num

private theorem prime_oneHundredSixteenDJ_182209 : Nat.Prime 182209 := by norm_num

private theorem prime_oneHundredSixteenDJ_182471 : Nat.Prime 182471 := by norm_num

private theorem prime_oneHundredSixteenDJ_187177 : Nat.Prime 187177 := by norm_num

private theorem prime_oneHundredSixteenDJ_188767 : Nat.Prime 188767 := by norm_num

private theorem prime_oneHundredSixteenDJ_190783 : Nat.Prime 190783 := by norm_num

private theorem prime_oneHundredSixteenDJ_198463 : Nat.Prime 198463 := by norm_num

private theorem prime_oneHundredSixteenDJ_217319 : Nat.Prime 217319 := by norm_num

private theorem prime_oneHundredSixteenDJ_235871 : Nat.Prime 235871 := by norm_num

private theorem prime_oneHundredSixteenDJ_239423 : Nat.Prime 239423 := by norm_num

private theorem prime_oneHundredSixteenDJ_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredSixteenDJ_262049 : Nat.Prime 262049 := by norm_num

private theorem prime_oneHundredSixteenDJ_265339 : Nat.Prime 265339 := by norm_num

private theorem prime_oneHundredSixteenDJ_266117 : Nat.Prime 266117 := by norm_num

private theorem prime_oneHundredSixteenDJ_271169 : Nat.Prime 271169 := by norm_num

private theorem prime_oneHundredSixteenDJ_273473 : Nat.Prime 273473 := by norm_num

private theorem prime_oneHundredSixteenDJ_281839 : Nat.Prime 281839 := by norm_num

private theorem prime_oneHundredSixteenDJ_282563 : Nat.Prime 282563 := by norm_num

private theorem prime_oneHundredSixteenDJ_286063 : Nat.Prime 286063 := by norm_num

private theorem prime_oneHundredSixteenDJ_291817 : Nat.Prime 291817 := by norm_num

private theorem prime_oneHundredSixteenDJ_293087 : Nat.Prime 293087 := by norm_num

private theorem prime_oneHundredSixteenDJ_300277 : Nat.Prime 300277 := by norm_num

private theorem prime_oneHundredSixteenDJ_309223 : Nat.Prime 309223 := by norm_num

private theorem prime_oneHundredSixteenDJ_309359 : Nat.Prime 309359 := by norm_num

private theorem prime_oneHundredSixteenDJ_316033 : Nat.Prime 316033 := by norm_num

private theorem prime_oneHundredSixteenDJ_316703 : Nat.Prime 316703 := by norm_num

private theorem prime_oneHundredSixteenDJ_319577 : Nat.Prime 319577 := by norm_num

private theorem prime_oneHundredSixteenDJ_321721 : Nat.Prime 321721 := by norm_num

private theorem prime_oneHundredSixteenDJ_326159 : Nat.Prime 326159 := by norm_num

private theorem prime_oneHundredSixteenDJ_327689 : Nat.Prime 327689 := by norm_num

private theorem prime_oneHundredSixteenDJ_347401 : Nat.Prime 347401 := by norm_num

private theorem prime_oneHundredSixteenDJ_357727 : Nat.Prime 357727 := by norm_num

private theorem prime_oneHundredSixteenDJ_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredSixteenDJ_367651 : Nat.Prime 367651 := by norm_num

private theorem prime_oneHundredSixteenDJ_387449 : Nat.Prime 387449 := by norm_num

private theorem prime_oneHundredSixteenDJ_410561 : Nat.Prime 410561 := by norm_num

private theorem prime_oneHundredSixteenDJ_414769 : Nat.Prime 414769 := by norm_num

private theorem prime_oneHundredSixteenDJ_415409 : Nat.Prime 415409 := by norm_num

private theorem prime_oneHundredSixteenDJ_425819 : Nat.Prime 425819 := by norm_num

private theorem prime_oneHundredSixteenDJ_438521 : Nat.Prime 438521 := by norm_num

private theorem prime_oneHundredSixteenDJ_495337 : Nat.Prime 495337 := by norm_num

private theorem prime_oneHundredSixteenDJ_542123 : Nat.Prime 542123 := by norm_num

private theorem prime_oneHundredSixteenDJ_554633 : Nat.Prime 554633 := by norm_num

private theorem prime_oneHundredSixteenDJ_564257 : Nat.Prime 564257 := by norm_num

private theorem prime_oneHundredSixteenDJ_599309 : Nat.Prime 599309 := by norm_num

private theorem prime_oneHundredSixteenDJ_635051 : Nat.Prime 635051 := by norm_num

private theorem prime_oneHundredSixteenDJ_673429 : Nat.Prime 673429 := by norm_num

private theorem prime_oneHundredSixteenDJ_761377 : Nat.Prime 761377 := by norm_num

private theorem prime_oneHundredSixteenDJ_783473 : Nat.Prime 783473 := by norm_num

private theorem prime_oneHundredSixteenDJ_825991 : Nat.Prime 825991 := by norm_num

private theorem prime_oneHundredSixteenDJ_867541 : Nat.Prime 867541 := by norm_num

private theorem prime_oneHundredSixteenDJ_899893 : Nat.Prime 899893 := by norm_num

private theorem prime_oneHundredSixteenDJ_924527 : Nat.Prime 924527 := by norm_num

private theorem prime_oneHundredSixteenDJ_936919 : Nat.Prime 936919 := by norm_num

private theorem prime_oneHundredSixteenDJ_941609 : Nat.Prime 941609 := by norm_num

private theorem prime_oneHundredSixteenDJ_984593 : Nat.Prime 984593 := by norm_num

private theorem prime_oneHundredSixteenDJ_988093 : Nat.Prime 988093 := by norm_num

private theorem prime_oneHundredSixteenDJ_1069223 : Nat.Prime 1069223 := by norm_num

private theorem prime_oneHundredSixteenDJ_1168859 : Nat.Prime 1168859 := by norm_num

private theorem prime_oneHundredSixteenDJ_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredSixteenDJ_1388473 : Nat.Prime 1388473 := by norm_num

private theorem prime_oneHundredSixteenDJ_1420277 : Nat.Prime 1420277 := by norm_num

private theorem prime_oneHundredSixteenDJ_1454149 : Nat.Prime 1454149 := by norm_num

private theorem prime_oneHundredSixteenDJ_1476581 : Nat.Prime 1476581 := by norm_num

private theorem prime_oneHundredSixteenDJ_1484459 : Nat.Prime 1484459 := by norm_num

private theorem prime_oneHundredSixteenDJ_1537169 : Nat.Prime 1537169 := by norm_num

private theorem prime_oneHundredSixteenDJ_1567067 : Nat.Prime 1567067 := by norm_num

private theorem prime_oneHundredSixteenDJ_1629923 : Nat.Prime 1629923 := by norm_num

private theorem prime_oneHundredSixteenDJ_1700341 : Nat.Prime 1700341 := by norm_num

private theorem prime_oneHundredSixteenDJ_1859831 : Nat.Prime 1859831 := by norm_num

private theorem prime_oneHundredSixteenDJ_1883621 : Nat.Prime 1883621 := by norm_num

private theorem prime_oneHundredSixteenDJ_1897669 : Nat.Prime 1897669 := by norm_num

private theorem prime_oneHundredSixteenDJ_1914439 : Nat.Prime 1914439 := by norm_num

private theorem prime_oneHundredSixteenDJ_2008879 : Nat.Prime 2008879 := by norm_num

private theorem prime_oneHundredSixteenDJ_2064437 : Nat.Prime 2064437 := by norm_num

private theorem prime_oneHundredSixteenDJ_2068039 : Nat.Prime 2068039 := by norm_num

private theorem prime_oneHundredSixteenDJ_2100071 : Nat.Prime 2100071 := by norm_num

private theorem prime_oneHundredSixteenDJ_2212187 : Nat.Prime 2212187 := by norm_num

private theorem prime_oneHundredSixteenDJ_2329997 : Nat.Prime 2329997 := by norm_num

private theorem prime_oneHundredSixteenDJ_2390911 : Nat.Prime 2390911 := by norm_num

private theorem prime_oneHundredSixteenDJ_2574499 : Nat.Prime 2574499 := by norm_num

private theorem prime_oneHundredSixteenDJ_2597011 : Nat.Prime 2597011 := by norm_num

private theorem prime_oneHundredSixteenDJ_2599747 : Nat.Prime 2599747 := by norm_num

private theorem prime_oneHundredSixteenDJ_2718109 : Nat.Prime 2718109 := by norm_num

private theorem prime_oneHundredSixteenDJ_2833553 : Nat.Prime 2833553 := by norm_num

private theorem prime_oneHundredSixteenDJ_3127219 : Nat.Prime 3127219 := by norm_num

private theorem prime_oneHundredSixteenDJ_3321761 : Nat.Prime 3321761 := by norm_num

private theorem prime_oneHundredSixteenDJ_3433061 : Nat.Prime 3433061 := by norm_num

private theorem prime_oneHundredSixteenDJ_3562193 : Nat.Prime 3562193 := by norm_num

private theorem prime_oneHundredSixteenDJ_3623897 : Nat.Prime 3623897 := by norm_num

private theorem prime_oneHundredSixteenDJ_3651731 : Nat.Prime 3651731 := by norm_num

private theorem prime_oneHundredSixteenDJ_3753137 : Nat.Prime 3753137 := by norm_num

private theorem prime_oneHundredSixteenDJ_4137359 : Nat.Prime 4137359 := by norm_num

private theorem prime_oneHundredSixteenDJ_4345609 : Nat.Prime 4345609 := by norm_num

private theorem prime_oneHundredSixteenDJ_4630697 : Nat.Prime 4630697 := by norm_num

private theorem prime_oneHundredSixteenDJ_4749047 : Nat.Prime 4749047 := by norm_num

private theorem prime_oneHundredSixteenDJ_4764211 : Nat.Prime 4764211 := by norm_num

private theorem prime_oneHundredSixteenDJ_4841303 : Nat.Prime 4841303 := by norm_num

private theorem prime_oneHundredSixteenDJ_4949221 : Nat.Prime 4949221 := by norm_num

private theorem prime_oneHundredSixteenDJ_5334911 : Nat.Prime 5334911 := by norm_num

private theorem prime_oneHundredSixteenDJ_6060581 : Nat.Prime 6060581 := by norm_num

private theorem prime_oneHundredSixteenDJ_6664139 : Nat.Prime 6664139 := by norm_num

private theorem prime_oneHundredSixteenDJ_6842149 : Nat.Prime 6842149 := by norm_num

private theorem prime_oneHundredSixteenDJ_6951563 : Nat.Prime 6951563 := by norm_num

private theorem prime_oneHundredSixteenDJ_6952349 : Nat.Prime 6952349 := by norm_num

private theorem prime_oneHundredSixteenDJ_7190737 : Nat.Prime 7190737 := by norm_num

private theorem prime_oneHundredSixteenDJ_7405967 : Nat.Prime 7405967 := by norm_num

private theorem prime_oneHundredSixteenDJ_7606559 : Nat.Prime 7606559 := by norm_num

private theorem prime_oneHundredSixteenDJ_7628339 : Nat.Prime 7628339 := by norm_num

private theorem prime_oneHundredSixteenDJ_8328919 : Nat.Prime 8328919 := by norm_num

private theorem prime_oneHundredSixteenDJ_8335031 : Nat.Prime 8335031 := by norm_num

private theorem prime_oneHundredSixteenDJ_8346469 : Nat.Prime 8346469 := by norm_num

private theorem prime_oneHundredSixteenDJ_8948279 : Nat.Prime 8948279 := by norm_num

private theorem prime_oneHundredSixteenDJ_9952799 : Nat.Prime 9952799 := by norm_num

private theorem prime_oneHundredSixteenDJ_10622309 : Nat.Prime 10622309 := by norm_num

private theorem prime_oneHundredSixteenDJ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixteenDJ_10832089 : Nat.Prime 10832089 := by norm_num

private theorem prime_oneHundredSixteenDJ_11126903 : Nat.Prime 11126903 := by norm_num

private theorem prime_oneHundredSixteenDJ_11649479 : Nat.Prime 11649479 := by norm_num

private theorem prime_oneHundredSixteenDJ_12292271 : Nat.Prime 12292271 := by norm_num

private theorem prime_oneHundredSixteenDJ_12515401 : Nat.Prime 12515401 := by norm_num

private theorem prime_oneHundredSixteenDJ_13902173 : Nat.Prime 13902173 := by norm_num

private theorem prime_oneHundredSixteenDJ_14729849 : Nat.Prime 14729849 := by norm_num

private theorem prime_oneHundredSixteenDJ_14856007 : Nat.Prime 14856007 := by norm_num

private theorem prime_oneHundredSixteenDJ_16069259 : Nat.Prime 16069259 := by norm_num

private theorem prime_oneHundredSixteenDJ_16519849 : Nat.Prime 16519849 := by norm_num

private theorem prime_oneHundredSixteenDJ_16637081 : Nat.Prime 16637081 := by norm_num

private theorem prime_oneHundredSixteenDJ_17041301 : Nat.Prime 17041301 := by norm_num

private theorem prime_oneHundredSixteenDJ_17166151 : Nat.Prime 17166151 := by norm_num

private theorem prime_oneHundredSixteenDJ_17181383 : Nat.Prime 17181383 := by norm_num

private theorem prime_oneHundredSixteenDJ_17881561 : Nat.Prime 17881561 := by norm_num

private theorem prime_oneHundredSixteenDJ_19622413 : Nat.Prime 19622413 := by norm_num

private theorem prime_oneHundredSixteenDJ_20009923 : Nat.Prime 20009923 := by norm_num

private theorem prime_oneHundredSixteenDJ_20323957 : Nat.Prime 20323957 := by norm_num

private theorem prime_oneHundredSixteenDJ_20369047 : Nat.Prime 20369047 := by norm_num

private theorem prime_oneHundredSixteenDJ_21157273 : Nat.Prime 21157273 := by norm_num

private theorem prime_oneHundredSixteenDJ_21522701 : Nat.Prime 21522701 := by norm_num

private theorem prime_oneHundredSixteenDJ_21675749 : Nat.Prime 21675749 := by norm_num

private theorem prime_oneHundredSixteenDJ_21873451 : Nat.Prime 21873451 := by norm_num

private theorem prime_oneHundredSixteenDJ_22946681 : Nat.Prime 22946681 := by norm_num

private theorem prime_oneHundredSixteenDJ_23525729 : Nat.Prime 23525729 := by norm_num

private theorem prime_oneHundredSixteenDJ_23897323 : Nat.Prime 23897323 := by norm_num

private theorem prime_oneHundredSixteenDJ_24086341 : Nat.Prime 24086341 := by norm_num

private theorem prime_oneHundredSixteenDJ_25556371 : Nat.Prime 25556371 := by norm_num

private theorem prime_oneHundredSixteenDJ_28016477 : Nat.Prime 28016477 := by norm_num

private theorem prime_oneHundredSixteenDJ_30606139 : Nat.Prime 30606139 := by
  apply lucas_primality 30606139 (2 : ZMod 30606139)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1700341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1700341, 1)] : List FactorBlock).map factorBlockValue).prod) = 30606139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_1700341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30606139) ^ 15303069 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30606139) ^ 10202046 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30606139) ^ 18 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_31602863 : Nat.Prime 31602863 := by
  apply lucas_primality 31602863 (5 : ZMod 31602863)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (41257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (41257, 1)] : List FactorBlock).map factorBlockValue).prod) = 31602863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_383
      · exact prime_oneHundredSixteenDJ_41257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 31602863) ^ 15801431 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 31602863) ^ 82514 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 31602863) ^ 766 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_35380903 : Nat.Prime 35380903 := by
  apply lucas_primality 35380903 (3 : ZMod 35380903)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (211, 1), (27947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (211, 1), (27947, 1)] : List FactorBlock).map factorBlockValue).prod) = 35380903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_211
      · exact prime_oneHundredSixteenDJ_27947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35380903) ^ 17690451 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35380903) ^ 11793634 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35380903) ^ 167682 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35380903) ^ 1266 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_38861267 : Nat.Prime 38861267 := by
  apply lucas_primality 38861267 (2 : ZMod 38861267)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (641, 1), (30313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (641, 1), (30313, 1)] : List FactorBlock).map factorBlockValue).prod) = 38861267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_641
      · exact prime_oneHundredSixteenDJ_30313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38861267) ^ 19430633 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 38861267) ^ 60626 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 38861267) ^ 1282 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_41175977 : Nat.Prime 41175977 := by
  apply lucas_primality 41175977 (3 : ZMod 41175977)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (84377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (84377, 1)] : List FactorBlock).map factorBlockValue).prod) = 41175977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_84377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41175977) ^ 20587988 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 41175977) ^ 675016 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 41175977) ^ 488 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_45482783 : Nat.Prime 45482783 := by
  apply lucas_primality 45482783 (5 : ZMod 45482783)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (59377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (59377, 1)] : List FactorBlock).map factorBlockValue).prod) = 45482783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_383
      · exact prime_oneHundredSixteenDJ_59377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45482783) ^ 22741391 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 45482783) ^ 118754 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 45482783) ^ 766 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_45893363 : Nat.Prime 45893363 := by
  apply lucas_primality 45893363 (2 : ZMod 45893363)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22946681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22946681, 1)] : List FactorBlock).map factorBlockValue).prod) = 45893363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_22946681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45893363) ^ 22946681 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45893363) ^ 2 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_50493167 : Nat.Prime 50493167 := by
  apply lucas_primality 50493167 (5 : ZMod 50493167)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (319577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (319577, 1)] : List FactorBlock).map factorBlockValue).prod) = 50493167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_79
      · exact prime_oneHundredSixteenDJ_319577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 50493167) ^ 25246583 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 50493167) ^ 639154 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 50493167) ^ 158 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_51850223 : Nat.Prime 51850223 := by
  apply lucas_primality 51850223 (5 : ZMod 51850223)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (134327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (134327, 1)] : List FactorBlock).map factorBlockValue).prod) = 51850223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_193
      · exact prime_oneHundredSixteenDJ_134327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 51850223) ^ 25925111 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 51850223) ^ 268654 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 51850223) ^ 386 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_51933437 : Nat.Prime 51933437 := by
  apply lucas_primality 51933437 (2 : ZMod 51933437)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (367, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (367, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 51933437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_367
      · exact prime_oneHundredSixteenDJ_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51933437) ^ 25966718 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51933437) ^ 3054908 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51933437) ^ 141508 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51933437) ^ 24956 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_52600043 : Nat.Prime 52600043 := by
  apply lucas_primality 52600043 (2 : ZMod 52600043)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2390911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2390911, 1)] : List FactorBlock).map factorBlockValue).prod) = 52600043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_2390911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52600043) ^ 26300021 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600043) ^ 4781822 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 52600043) ^ 22 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_59887673 : Nat.Prime 59887673 := by
  apply lucas_primality 59887673 (3 : ZMod 59887673)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (179, 1), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (179, 1), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) = 59887673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_179
      · exact prime_oneHundredSixteenDJ_3217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59887673) ^ 29943836 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59887673) ^ 4606744 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59887673) ^ 334568 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59887673) ^ 18616 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_1811
      · exact prime_oneHundredSixteenDJ_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_60015647 : Nat.Prime 60015647 := by
  apply lucas_primality 60015647 (5 : ZMod 60015647)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (309359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (309359, 1)] : List FactorBlock).map factorBlockValue).prod) = 60015647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_97
      · exact prime_oneHundredSixteenDJ_309359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 60015647) ^ 30007823 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 60015647) ^ 618718 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 60015647) ^ 194 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_61664261 : Nat.Prime 61664261 := by
  apply lucas_primality 61664261 (2 : ZMod 61664261)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (337, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (337, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) = 61664261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_337
      · exact prime_oneHundredSixteenDJ_1307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61664261) ^ 30832130 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61664261) ^ 12332852 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61664261) ^ 8809180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61664261) ^ 182980 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61664261) ^ 47180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_63138997 : Nat.Prime 63138997 := by
  apply lucas_primality 63138997 (2 : ZMod 63138997)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1283, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1283, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) = 63138997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_1283
      · exact prime_oneHundredSixteenDJ_1367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63138997) ^ 31569498 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63138997) ^ 21046332 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63138997) ^ 49212 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63138997) ^ 46188 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_77269033 : Nat.Prime 77269033 := by
  apply lucas_primality 77269033 (5 : ZMod 77269033)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (357727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (357727, 1)] : List FactorBlock).map factorBlockValue).prod) = 77269033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_357727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 77269033) ^ 38634516 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 77269033) ^ 25756344 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 77269033) ^ 216 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_77854541 : Nat.Prime 77854541 := by
  apply lucas_primality 77854541 (2 : ZMod 77854541)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (169249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (169249, 1)] : List FactorBlock).map factorBlockValue).prod) = 77854541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_169249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77854541) ^ 38927270 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77854541) ^ 15570908 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77854541) ^ 3384980 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77854541) ^ 460 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_94617863 : Nat.Prime 94617863 := by
  apply lucas_primality 94617863 (5 : ZMod 94617863)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (787, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (787, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 94617863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_47
      · exact prime_oneHundredSixteenDJ_787
      · exact prime_oneHundredSixteenDJ_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 94617863) ^ 47308931 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 94617863) ^ 2013146 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 94617863) ^ 120226 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 94617863) ^ 73978 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_97461977 : Nat.Prime 97461977 := by
  apply lucas_primality 97461977 (3 : ZMod 97461977)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (709, 1), (17183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (709, 1), (17183, 1)] : List FactorBlock).map factorBlockValue).prod) = 97461977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_709
      · exact prime_oneHundredSixteenDJ_17183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 97461977) ^ 48730988 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 97461977) ^ 137464 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 97461977) ^ 5672 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_99620189 : Nat.Prime 99620189 := by
  apply lucas_primality 99620189 (2 : ZMod 99620189)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (179173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (179173, 1)] : List FactorBlock).map factorBlockValue).prod) = 99620189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_139
      · exact prime_oneHundredSixteenDJ_179173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 99620189) ^ 49810094 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 99620189) ^ 716692 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 99620189) ^ 556 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_102247807 : Nat.Prime 102247807 := by
  apply lucas_primality 102247807 (3 : ZMod 102247807)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17041301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17041301, 1)] : List FactorBlock).map factorBlockValue).prod) = 102247807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17041301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102247807) ^ 51123903 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102247807) ^ 34082602 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102247807) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_103317769 : Nat.Prime 103317769 := by
  apply lucas_primality 103317769 (23 : ZMod 103317769)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (53147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (53147, 1)] : List FactorBlock).map factorBlockValue).prod) = 103317769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_53147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 103317769) ^ 51658884 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 103317769) ^ 34439256 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 103317769) ^ 1944 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_117734479 : Nat.Prime 117734479 := by
  apply lucas_primality 117734479 (3 : ZMod 117734479)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19622413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19622413, 1)] : List FactorBlock).map factorBlockValue).prod) = 117734479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_19622413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 117734479) ^ 58867239 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 117734479) ^ 39244826 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 117734479) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_117934951 : Nat.Prime 117934951 := by
  apply lucas_primality 117934951 (23 : ZMod 117934951)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (6607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (6607, 1)] : List FactorBlock).map factorBlockValue).prod) = 117934951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_6607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 117934951) ^ 58967475 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 39311650 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 23586990 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 16847850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 6937350 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 17850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_119579497 : Nat.Prime 119579497 := by
  apply lucas_primality 119579497 (5 : ZMod 119579497)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (293087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (293087, 1)] : List FactorBlock).map factorBlockValue).prod) = 119579497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_293087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119579497) ^ 59789748 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 119579497) ^ 39859832 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 119579497) ^ 7034088 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 119579497) ^ 408 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_120796301 : Nat.Prime 120796301 := by
  apply lucas_primality 120796301 (3 : ZMod 120796301)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (63577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (63577, 1)] : List FactorBlock).map factorBlockValue).prod) = 120796301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_63577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120796301) ^ 60398150 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 120796301) ^ 24159260 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 120796301) ^ 6357700 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 120796301) ^ 1900 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_122424557 : Nat.Prime 122424557 := by
  apply lucas_primality 122424557 (2 : ZMod 122424557)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (30606139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (30606139, 1)] : List FactorBlock).map factorBlockValue).prod) = 122424557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_30606139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 122424557) ^ 61212278 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 122424557) ^ 4 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_125154011 : Nat.Prime 125154011 := by
  apply lucas_primality 125154011 (6 : ZMod 125154011)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12515401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12515401, 1)] : List FactorBlock).map factorBlockValue).prod) = 125154011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_12515401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 125154011) ^ 62577005 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 125154011) ^ 25030802 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 125154011) ^ 10 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_130460293 : Nat.Prime 130460293 := by
  apply lucas_primality 130460293 (2 : ZMod 130460293)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3623897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3623897, 1)] : List FactorBlock).map factorBlockValue).prod) = 130460293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_3623897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 130460293) ^ 65230146 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 130460293) ^ 43486764 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 130460293) ^ 36 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_140392471 : Nat.Prime 140392471 := by
  apply lucas_primality 140392471 (6 : ZMod 140392471)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (69847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (69847, 1)] : List FactorBlock).map factorBlockValue).prod) = 140392471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_67
      · exact prime_oneHundredSixteenDJ_69847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140392471) ^ 70196235 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392471) ^ 46797490 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392471) ^ 28078494 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392471) ^ 2095410 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392471) ^ 2010 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_159028123 : Nat.Prime 159028123 := by
  apply lucas_primality 159028123 (13 : ZMod 159028123)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (317, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (317, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 159028123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_317
      · exact prime_oneHundredSixteenDJ_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 159028123) ^ 79514061 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 159028123) ^ 53009374 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 159028123) ^ 14457102 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 159028123) ^ 501666 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 159028123) ^ 230142 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_186570341 : Nat.Prime 186570341 := by
  apply lucas_primality 186570341 (2 : ZMod 186570341)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (29, 1), (29243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (29, 1), (29243, 1)] : List FactorBlock).map factorBlockValue).prod) = 186570341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_29243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186570341) ^ 93285170 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 186570341) ^ 37314068 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 186570341) ^ 16960940 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 186570341) ^ 6433460 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 186570341) ^ 6380 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_194395667 : Nat.Prime 194395667 := by
  apply lucas_primality 194395667 (2 : ZMod 194395667)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (2068039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (2068039, 1)] : List FactorBlock).map factorBlockValue).prod) = 194395667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_47
      · exact prime_oneHundredSixteenDJ_2068039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 194395667) ^ 97197833 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 194395667) ^ 4136078 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 194395667) ^ 94 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_205993813 : Nat.Prime 205993813 := by
  apply lucas_primality 205993813 (2 : ZMod 205993813)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17166151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17166151, 1)] : List FactorBlock).map factorBlockValue).prod) = 205993813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17166151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 205993813) ^ 102996906 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 205993813) ^ 68664604 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 205993813) ^ 12 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_212285419 : Nat.Prime 212285419 := by
  apply lucas_primality 212285419 (2 : ZMod 212285419)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35380903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35380903, 1)] : List FactorBlock).map factorBlockValue).prod) = 212285419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_35380903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 212285419) ^ 106142709 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 212285419) ^ 70761806 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 212285419) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_292985027 : Nat.Prime 292985027 := by
  apply lucas_primality 292985027 (2 : ZMod 292985027)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1607, 1), (91159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1607, 1), (91159, 1)] : List FactorBlock).map factorBlockValue).prod) = 292985027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_1607
      · exact prime_oneHundredSixteenDJ_91159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 292985027) ^ 146492513 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 292985027) ^ 182318 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 292985027) ^ 3214 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_294409061 : Nat.Prime 294409061 := by
  apply lucas_primality 294409061 (2 : ZMod 294409061)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (17, 1), (223, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (17, 1), (223, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) = 294409061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_223
      · exact prime_oneHundredSixteenDJ_353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294409061) ^ 147204530 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 294409061) ^ 58881812 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 294409061) ^ 26764460 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 294409061) ^ 17318180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 294409061) ^ 1320220 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 294409061) ^ 834020 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_359326039 : Nat.Prime 359326039 := by
  apply lucas_primality 359326039 (6 : ZMod 359326039)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59887673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59887673, 1)] : List FactorBlock).map factorBlockValue).prod) = 359326039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_59887673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 359326039) ^ 179663019 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 359326039) ^ 119775346 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 359326039) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_380305279 : Nat.Prime 380305279 := by
  apply lucas_primality 380305279 (6 : ZMod 380305279)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (151, 1), (139921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (151, 1), (139921, 1)] : List FactorBlock).map factorBlockValue).prod) = 380305279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_151
      · exact prime_oneHundredSixteenDJ_139921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 380305279) ^ 190152639 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 380305279) ^ 126768426 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 380305279) ^ 2518578 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 380305279) ^ 2718 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_388978549 : Nat.Prime 388978549 := by
  apply lucas_primality 388978549 (10 : ZMod 388978549)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (4630697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (4630697, 1)] : List FactorBlock).map factorBlockValue).prod) = 388978549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_4630697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 388978549) ^ 194489274 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 388978549) ^ 129659516 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 388978549) ^ 55568364 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 388978549) ^ 84 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_395840099 : Nat.Prime 395840099 := by
  apply lucas_primality 395840099 (2 : ZMod 395840099)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4967, 1), (39847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4967, 1), (39847, 1)] : List FactorBlock).map factorBlockValue).prod) = 395840099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_4967
      · exact prime_oneHundredSixteenDJ_39847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 395840099) ^ 197920049 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 395840099) ^ 79694 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 395840099) ^ 9934 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_403945337 : Nat.Prime 403945337 := by
  apply lucas_primality 403945337 (3 : ZMod 403945337)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (50493167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (50493167, 1)] : List FactorBlock).map factorBlockValue).prod) = 403945337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_50493167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 403945337) ^ 201972668 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 403945337) ^ 8 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_406538471 : Nat.Prime 406538471 := by
  apply lucas_primality 406538471 (11 : ZMod 406538471)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (3127219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (3127219, 1)] : List FactorBlock).map factorBlockValue).prod) = 406538471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_3127219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 406538471) ^ 203269235 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 406538471) ^ 81307694 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 406538471) ^ 31272190 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 406538471) ^ 130 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_424416887 : Nat.Prime 424416887 := by
  apply lucas_primality 424416887 (5 : ZMod 424416887)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (92789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (92789, 1)] : List FactorBlock).map factorBlockValue).prod) = 424416887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_2287
      · exact prime_oneHundredSixteenDJ_92789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 424416887) ^ 212208443 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 424416887) ^ 185578 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 424416887) ^ 4574 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_451061227 : Nat.Prime 451061227 := by
  apply lucas_primality 451061227 (3 : ZMod 451061227)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (503, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (503, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 451061227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_503
      · exact prime_oneHundredSixteenDJ_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 451061227) ^ 225530613 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 150353742 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 64437318 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 41005566 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 896742 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 697158 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_496820591 : Nat.Prime 496820591 := by
  apply lucas_primality 496820591 (7 : ZMod 496820591)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (919, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (919, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) = 496820591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_919
      · exact prime_oneHundredSixteenDJ_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 496820591) ^ 248410295 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 496820591) ^ 99364118 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 496820591) ^ 70974370 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 496820591) ^ 540610 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 496820591) ^ 64330 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_545793397 : Nat.Prime 545793397 := by
  apply lucas_primality 545793397 (6 : ZMod 545793397)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (45482783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (45482783, 1)] : List FactorBlock).map factorBlockValue).prod) = 545793397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_45482783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 545793397) ^ 272896698 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 545793397) ^ 181931132 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 545793397) ^ 12 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_564617497 : Nat.Prime 564617497 := by
  apply lucas_primality 564617497 (5 : ZMod 564617497)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23525729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23525729, 1)] : List FactorBlock).map factorBlockValue).prod) = 564617497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_23525729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 564617497) ^ 282308748 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 564617497) ^ 188205832 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 564617497) ^ 24 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_565347311 : Nat.Prime 565347311 := by
  apply lucas_primality 565347311 (11 : ZMod 565347311)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (31, 1), (317, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (31, 1), (317, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 565347311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_31
      · exact prime_oneHundredSixteenDJ_317
      · exact prime_oneHundredSixteenDJ_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 565347311) ^ 282673655 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 565347311) ^ 113069462 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 565347311) ^ 51395210 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 565347311) ^ 18237010 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 565347311) ^ 1783430 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 565347311) ^ 1080970 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_611108941 : Nat.Prime 611108941 := by
  apply lucas_primality 611108941 (6 : ZMod 611108941)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (783473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (783473, 1)] : List FactorBlock).map factorBlockValue).prod) = 611108941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_783473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 611108941) ^ 305554470 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 611108941) ^ 203702980 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 611108941) ^ 122221788 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 611108941) ^ 47008380 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 611108941) ^ 780 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_643516777 : Nat.Prime 643516777 := by
  apply lucas_primality 643516777 (5 : ZMod 643516777)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (17, 1), (19, 1), (59, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (17, 1), (19, 1), (59, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) = 643516777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_59
      · exact prime_oneHundredSixteenDJ_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 643516777) ^ 321758388 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 643516777) ^ 214505592 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 643516777) ^ 91930968 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 643516777) ^ 37853928 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 643516777) ^ 33869304 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 643516777) ^ 10907064 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 643516777) ^ 9604728 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_677911001 : Nat.Prime 677911001 := by
  apply lucas_primality 677911001 (3 : ZMod 677911001)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (13, 1), (52147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (13, 1), (52147, 1)] : List FactorBlock).map factorBlockValue).prod) = 677911001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_52147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 677911001) ^ 338955500 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 677911001) ^ 135582200 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 677911001) ^ 52147000 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 677911001) ^ 13000 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17203
      · exact prime_oneHundredSixteenDJ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_786808669 : Nat.Prime 786808669 := by
  apply lucas_primality 786808669 (7 : ZMod 786808669)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 2), (35461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 2), (35461, 1)] : List FactorBlock).map factorBlockValue).prod) = 786808669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_43
      · exact prime_oneHundredSixteenDJ_35461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 786808669) ^ 393404334 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 786808669) ^ 262269556 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 786808669) ^ 18297876 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 786808669) ^ 22188 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_842354827 : Nat.Prime 842354827 := by
  apply lucas_primality 842354827 (2 : ZMod 842354827)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (140392471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (140392471, 1)] : List FactorBlock).map factorBlockValue).prod) = 842354827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_140392471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 842354827) ^ 421177413 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 842354827) ^ 280784942 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 842354827) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_922858723 : Nat.Prime 922858723 := by
  apply lucas_primality 922858723 (3 : ZMod 922858723)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3329, 1), (15401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3329, 1), (15401, 1)] : List FactorBlock).map factorBlockValue).prod) = 922858723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_3329
      · exact prime_oneHundredSixteenDJ_15401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 922858723) ^ 461429361 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 922858723) ^ 307619574 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 922858723) ^ 277218 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 922858723) ^ 59922 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_958344917 : Nat.Prime 958344917 := by
  apply lucas_primality 958344917 (2 : ZMod 958344917)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2767, 1), (86587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2767, 1), (86587, 1)] : List FactorBlock).map factorBlockValue).prod) = 958344917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_2767
      · exact prime_oneHundredSixteenDJ_86587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 958344917) ^ 479172458 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 958344917) ^ 346348 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 958344917) ^ 11068 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_964187701 : Nat.Prime 964187701 := by
  apply lucas_primality 964187701 (2 : ZMod 964187701)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 2), (107, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 2), (107, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 964187701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_107
      · exact prime_oneHundredSixteenDJ_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 964187701) ^ 482093850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 964187701) ^ 321395900 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 964187701) ^ 192837540 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 964187701) ^ 137741100 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 964187701) ^ 9011100 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 964187701) ^ 1572900 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_993641183 : Nat.Prime 993641183 := by
  apply lucas_primality 993641183 (5 : ZMod 993641183)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (496820591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (496820591, 1)] : List FactorBlock).map factorBlockValue).prod) = 993641183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_496820591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 993641183) ^ 496820591 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 993641183) ^ 2 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1068723629 : Nat.Prime 1068723629 := by
  apply lucas_primality 1068723629 (2 : ZMod 1068723629)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (2008879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (2008879, 1)] : List FactorBlock).map factorBlockValue).prod) = 1068723629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_2008879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1068723629) ^ 534361814 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1068723629) ^ 152674804 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1068723629) ^ 56248612 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1068723629) ^ 532 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1079547257 : Nat.Prime 1079547257 := by
  apply lucas_primality 1079547257 (3 : ZMod 1079547257)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (2212187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (2212187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079547257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_2212187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1079547257) ^ 539773628 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1079547257) ^ 17697496 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1079547257) ^ 488 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1082486417 : Nat.Prime 1082486417 := by
  apply lucas_primality 1082486417 (3 : ZMod 1082486417)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (53, 1), (116047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (53, 1), (116047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1082486417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_53
      · exact prime_oneHundredSixteenDJ_116047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1082486417) ^ 541243208 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1082486417) ^ 98407856 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1082486417) ^ 20424272 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1082486417) ^ 9328 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1101440713 : Nat.Prime 1101440713 := by
  apply lucas_primality 1101440713 (10 : ZMod 1101440713)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (45893363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (45893363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101440713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_45893363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1101440713) ^ 550720356 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1101440713) ^ 367146904 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1101440713) ^ 24 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1170701299 : Nat.Prime 1170701299 := by
  apply lucas_primality 1170701299 (3 : ZMod 1170701299)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (31, 1), (161387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (31, 1), (161387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1170701299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_31
      · exact prime_oneHundredSixteenDJ_161387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1170701299) ^ 585350649 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1170701299) ^ 390233766 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1170701299) ^ 90053946 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1170701299) ^ 37764558 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1170701299) ^ 7254 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1267727987 : Nat.Prime 1267727987 := by
  apply lucas_primality 1267727987 (2 : ZMod 1267727987)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (1484459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (1484459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267727987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_1484459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1267727987) ^ 633863993 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267727987) ^ 181103998 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267727987) ^ 20782426 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267727987) ^ 854 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1497202607 : Nat.Prime 1497202607 := by
  apply lucas_primality 1497202607 (5 : ZMod 1497202607)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (487, 1), (1537169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (487, 1), (1537169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497202607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_487
      · exact prime_oneHundredSixteenDJ_1537169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1497202607) ^ 748601303 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1497202607) ^ 3074338 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1497202607) ^ 974 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1519423693 : Nat.Prime 1519423693 := by
  apply lucas_primality 1519423693 (5 : ZMod 1519423693)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (6664139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (6664139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1519423693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_6664139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1519423693) ^ 759711846 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1519423693) ^ 506474564 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1519423693) ^ 79969668 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1519423693) ^ 228 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1633321477 : Nat.Prime 1633321477 := by
  apply lucas_primality 1633321477 (2 : ZMod 1633321477)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (83, 1), (182209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (83, 1), (182209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1633321477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_83
      · exact prime_oneHundredSixteenDJ_182209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1633321477) ^ 816660738 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633321477) ^ 544440492 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633321477) ^ 19678572 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633321477) ^ 8964 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1669035451 : Nat.Prime 1669035451 := by
  apply lucas_primality 1669035451 (3 : ZMod 1669035451)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11126903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11126903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1669035451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11126903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1669035451) ^ 834517725 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1669035451) ^ 556345150 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1669035451) ^ 333807090 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1669035451) ^ 150 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1685024599 : Nat.Prime 1685024599 := by
  apply lucas_primality 1685024599 (3 : ZMod 1685024599)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (16519849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (16519849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1685024599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_16519849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1685024599) ^ 842512299 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1685024599) ^ 561674866 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1685024599) ^ 99119094 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1685024599) ^ 102 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1687213519 : Nat.Prime 1687213519 := by
  apply lucas_primality 1687213519 (6 : ZMod 1687213519)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (61, 1), (271169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (61, 1), (271169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1687213519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_271169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1687213519) ^ 843606759 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1687213519) ^ 562404506 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1687213519) ^ 99247854 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1687213519) ^ 27659238 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1687213519) ^ 6222 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1757910163 : Nat.Prime 1757910163 := by
  apply lucas_primality 1757910163 (3 : ZMod 1757910163)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (292985027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (292985027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1757910163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_292985027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1757910163) ^ 878955081 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757910163) ^ 585970054 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757910163) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2009402137 : Nat.Prime 2009402137 := by
  apply lucas_primality 2009402137 (10 : ZMod 2009402137)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (317, 1), (12577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (317, 1), (12577, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009402137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_317
      · exact prime_oneHundredSixteenDJ_12577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2009402137) ^ 1004701068 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2009402137) ^ 669800712 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2009402137) ^ 287057448 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2009402137) ^ 6338808 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2009402137) ^ 159768 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2123067029 : Nat.Prime 2123067029 := by
  apply lucas_primality 2123067029 (2 : ZMod 2123067029)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (3562193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (3562193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2123067029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_149
      · exact prime_oneHundredSixteenDJ_3562193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2123067029) ^ 1061533514 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2123067029) ^ 14248772 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2123067029) ^ 596 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2283421873 : Nat.Prime 2283421873 := by
  apply lucas_primality 2283421873 (5 : ZMod 2283421873)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2731, 1), (17419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2731, 1), (17419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2283421873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_2731
      · exact prime_oneHundredSixteenDJ_17419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2283421873) ^ 1141710936 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2283421873) ^ 761140624 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2283421873) ^ 836112 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2283421873) ^ 131088 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2329702477 : Nat.Prime 2329702477 := by
  apply lucas_primality 2329702477 (5 : ZMod 2329702477)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (269, 1), (31379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (269, 1), (31379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329702477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_269
      · exact prime_oneHundredSixteenDJ_31379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2329702477) ^ 1164851238 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2329702477) ^ 776567492 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2329702477) ^ 101291412 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2329702477) ^ 8660604 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2329702477) ^ 74244 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2364353171 : Nat.Prime 2364353171 := by
  apply lucas_primality 2364353171 (2 : ZMod 2364353171)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2677, 1), (88321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2677, 1), (88321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364353171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_2677
      · exact prime_oneHundredSixteenDJ_88321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2364353171) ^ 1182176585 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364353171) ^ 472870634 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364353171) ^ 883210 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364353171) ^ 26770 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_47
      · exact prime_oneHundredSixteenDJ_71
      · exact prime_oneHundredSixteenDJ_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2554578179 : Nat.Prime 2554578179 := by
  apply lucas_primality 2554578179 (2 : ZMod 2554578179)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7963, 1), (160403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7963, 1), (160403, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554578179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7963
      · exact prime_oneHundredSixteenDJ_160403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2554578179) ^ 1277289089 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2554578179) ^ 320806 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2554578179) ^ 15926 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2564843623 : Nat.Prime 2564843623 := by
  apply lucas_primality 2564843623 (3 : ZMod 2564843623)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (38861267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (38861267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2564843623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_38861267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2564843623) ^ 1282421811 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2564843623) ^ 854947874 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2564843623) ^ 233167602 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2564843623) ^ 66 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2960664041 : Nat.Prime 2960664041 := by
  apply lucas_primality 2960664041 (3 : ZMod 2960664041)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (79, 1), (936919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (79, 1), (936919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2960664041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_79
      · exact prime_oneHundredSixteenDJ_936919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2960664041) ^ 1480332020 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2960664041) ^ 592132808 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2960664041) ^ 37476760 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2960664041) ^ 3160 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3369419309 : Nat.Prime 3369419309 := by
  apply lucas_primality 3369419309 (2 : ZMod 3369419309)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (842354827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (842354827, 1)] : List FactorBlock).map factorBlockValue).prod) = 3369419309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_842354827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3369419309) ^ 1684709654 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3369419309) ^ 4 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3526779199 : Nat.Prime 3526779199 := by
  apply lucas_primality 3526779199 (6 : ZMod 3526779199)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (25556371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (25556371, 1)] : List FactorBlock).map factorBlockValue).prod) = 3526779199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_25556371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3526779199) ^ 1763389599 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3526779199) ^ 1175593066 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3526779199) ^ 153338226 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3526779199) ^ 138 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3699855661 : Nat.Prime 3699855661 := by
  apply lucas_primality 3699855661 (6 : ZMod 3699855661)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61664261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61664261, 1)] : List FactorBlock).map factorBlockValue).prod) = 3699855661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_61664261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3699855661) ^ 1849927830 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3699855661) ^ 1233285220 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3699855661) ^ 739971132 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3699855661) ^ 60 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3760206607 : Nat.Prime 3760206607 := by
  apply lucas_primality 3760206607 (3 : ZMod 3760206607)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (16069259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (16069259, 1)] : List FactorBlock).map factorBlockValue).prod) = 3760206607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_16069259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3760206607) ^ 1880103303 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3760206607) ^ 1253402202 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3760206607) ^ 289246662 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3760206607) ^ 234 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3925953061 : Nat.Prime 3925953061 := by
  apply lucas_primality 3925953061 (2 : ZMod 3925953061)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1409, 1), (46439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1409, 1), (46439, 1)] : List FactorBlock).map factorBlockValue).prod) = 3925953061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_1409
      · exact prime_oneHundredSixteenDJ_46439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3925953061) ^ 1962976530 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3925953061) ^ 1308651020 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3925953061) ^ 785190612 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3925953061) ^ 2786340 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3925953061) ^ 84540 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5315870831 : Nat.Prime 5315870831 := by
  apply lucas_primality 5315870831 (13 : ZMod 5315870831)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (887, 1), (599309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (887, 1), (599309, 1)] : List FactorBlock).map factorBlockValue).prod) = 5315870831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_887
      · exact prime_oneHundredSixteenDJ_599309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 5315870831) ^ 2657935415 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 5315870831) ^ 1063174166 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 5315870831) ^ 5993090 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 5315870831) ^ 8870 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5416745897 : Nat.Prime 5416745897 := by
  apply lucas_primality 5416745897 (3 : ZMod 5416745897)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (263, 1), (2574499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (263, 1), (2574499, 1)] : List FactorBlock).map factorBlockValue).prod) = 5416745897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_263
      · exact prime_oneHundredSixteenDJ_2574499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5416745897) ^ 2708372948 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5416745897) ^ 20595992 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5416745897) ^ 2104 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5918493551 : Nat.Prime 5918493551 := by
  apply lucas_primality 5918493551 (11 : ZMod 5918493551)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (59, 1), (229, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (59, 1), (229, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) = 5918493551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_59
      · exact prime_oneHundredSixteenDJ_229
      · exact prime_oneHundredSixteenDJ_8761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5918493551) ^ 2959246775 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5918493551) ^ 1183698710 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5918493551) ^ 100313450 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5918493551) ^ 25844950 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5918493551) ^ 675550 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5931436409 : Nat.Prime 5931436409 := by
  apply lucas_primality 5931436409 (3 : ZMod 5931436409)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (353, 1), (123551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (353, 1), (123551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5931436409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_353
      · exact prime_oneHundredSixteenDJ_123551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5931436409) ^ 2965718204 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5931436409) ^ 348908024 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5931436409) ^ 16802936 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5931436409) ^ 48008 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_6010668571 : Nat.Prime 6010668571 := by
  apply lucas_primality 6010668571 (10 : ZMod 6010668571)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (101, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (101, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) = 6010668571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_43
      · exact prime_oneHundredSixteenDJ_101
      · exact prime_oneHundredSixteenDJ_46133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6010668571) ^ 3005334285 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 6010668571) ^ 2003556190 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 6010668571) ^ 1202133714 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 6010668571) ^ 139782990 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 6010668571) ^ 59511570 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 6010668571) ^ 130290 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_31
      · exact prime_oneHundredSixteenDJ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_7031640653 : Nat.Prime 7031640653 := by
  apply lucas_primality 7031640653 (2 : ZMod 7031640653)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1757910163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1757910163, 1)] : List FactorBlock).map factorBlockValue).prod) = 7031640653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_1757910163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7031640653) ^ 3515820326 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7031640653) ^ 4 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_7462005923 : Nat.Prime 7462005923 := by
  apply lucas_primality 7462005923 (2 : ZMod 7462005923)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14009, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14009, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) = 7462005923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_14009
      · exact prime_oneHundredSixteenDJ_38047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7462005923) ^ 3731002961 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7462005923) ^ 1066000846 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7462005923) ^ 532658 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7462005923) ^ 196126 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_7666759337 : Nat.Prime 7666759337 := by
  apply lucas_primality 7666759337 (3 : ZMod 7666759337)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (958344917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (958344917, 1)] : List FactorBlock).map factorBlockValue).prod) = 7666759337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_958344917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7666759337) ^ 3833379668 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7666759337) ^ 8 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_8308577099 : Nat.Prime 8308577099 := by
  apply lucas_primality 8308577099 (2 : ZMod 8308577099)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (97, 1), (542123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (97, 1), (542123, 1)] : List FactorBlock).map factorBlockValue).prod) = 8308577099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_79
      · exact prime_oneHundredSixteenDJ_97
      · exact prime_oneHundredSixteenDJ_542123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8308577099) ^ 4154288549 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8308577099) ^ 105171862 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8308577099) ^ 85655434 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8308577099) ^ 15326 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_8333873987 : Nat.Prime 8333873987 := by
  apply lucas_primality 8333873987 (2 : ZMod 8333873987)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (24086341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (24086341, 1)] : List FactorBlock).map factorBlockValue).prod) = 8333873987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_173
      · exact prime_oneHundredSixteenDJ_24086341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8333873987) ^ 4166936993 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8333873987) ^ 48172682 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8333873987) ^ 346 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_9799928863 : Nat.Prime 9799928863 := by
  apply lucas_primality 9799928863 (3 : ZMod 9799928863)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1633321477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1633321477, 1)] : List FactorBlock).map factorBlockValue).prod) = 9799928863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_1633321477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9799928863) ^ 4899964431 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9799928863) ^ 3266642954 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9799928863) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_10522995737 : Nat.Prime 10522995737 := by
  apply lucas_primality 10522995737 (3 : ZMod 10522995737)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (119579497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (119579497, 1)] : List FactorBlock).map factorBlockValue).prod) = 10522995737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_119579497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10522995737) ^ 5261497868 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10522995737) ^ 956635976 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10522995737) ^ 88 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_13173803039 : Nat.Prime 13173803039 := by
  apply lucas_primality 13173803039 (11 : ZMod 13173803039)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (257, 1), (2329997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (257, 1), (2329997, 1)] : List FactorBlock).map factorBlockValue).prod) = 13173803039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_257
      · exact prime_oneHundredSixteenDJ_2329997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 13173803039) ^ 6586901519 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13173803039) ^ 1197618458 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13173803039) ^ 51259934 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13173803039) ^ 5654 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_13275652681 : Nat.Prime 13275652681 := by
  apply lucas_primality 13275652681 (19 : ZMod 13275652681)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (12292271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (12292271, 1)] : List FactorBlock).map factorBlockValue).prod) = 13275652681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_12292271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 13275652681) ^ 6637826340 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13275652681) ^ 4425217560 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13275652681) ^ 2655130536 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13275652681) ^ 1080 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_13339342297 : Nat.Prime 13339342297 := by
  apply lucas_primality 13339342297 (5 : ZMod 13339342297)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (101, 1), (262049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (101, 1), (262049, 1)] : List FactorBlock).map factorBlockValue).prod) = 13339342297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_101
      · exact prime_oneHundredSixteenDJ_262049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13339342297) ^ 6669671148 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13339342297) ^ 4446447432 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13339342297) ^ 1905620328 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13339342297) ^ 132072696 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13339342297) ^ 50904 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_16494175361 : Nat.Prime 16494175361 := by
  apply lucas_primality 16494175361 (3 : ZMod 16494175361)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (13, 1), (41, 1), (48353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (13, 1), (41, 1), (48353, 1)] : List FactorBlock).map factorBlockValue).prod) = 16494175361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_48353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16494175361) ^ 8247087680 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16494175361) ^ 3298835072 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16494175361) ^ 1268782720 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16494175361) ^ 402296960 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16494175361) ^ 341120 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_20478070891 : Nat.Prime 20478070891 := by
  apply lucas_primality 20478070891 (2 : ZMod 20478070891)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (109, 1), (137, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (109, 1), (137, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 20478070891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_109
      · exact prime_oneHundredSixteenDJ_137
      · exact prime_oneHundredSixteenDJ_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20478070891) ^ 10239035445 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20478070891) ^ 6826023630 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20478070891) ^ 4095614178 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20478070891) ^ 187872210 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20478070891) ^ 149474970 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20478070891) ^ 12095730 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_21088424999 : Nat.Prime 21088424999 := by
  apply lucas_primality 21088424999 (11 : ZMod 21088424999)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (63138997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (63138997, 1)] : List FactorBlock).map factorBlockValue).prod) = 21088424999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_167
      · exact prime_oneHundredSixteenDJ_63138997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 21088424999) ^ 10544212499 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 21088424999) ^ 126277994 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 21088424999) ^ 334 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_22199133967 : Nat.Prime 22199133967 := by
  apply lucas_primality 22199133967 (3 : ZMod 22199133967)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3699855661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3699855661, 1)] : List FactorBlock).map factorBlockValue).prod) = 22199133967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_3699855661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22199133967) ^ 11099566983 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 22199133967) ^ 7399711322 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 22199133967) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_22687582991 : Nat.Prime 22687582991 := by
  apply lucas_primality 22687582991 (13 : ZMod 22687582991)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (211, 1), (359, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (211, 1), (359, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 22687582991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_211
      · exact prime_oneHundredSixteenDJ_359
      · exact prime_oneHundredSixteenDJ_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22687582991) ^ 11343791495 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22687582991) ^ 4537516598 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22687582991) ^ 371927590 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22687582991) ^ 107524090 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22687582991) ^ 63196610 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22687582991) ^ 46206890 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_24894627137 : Nat.Prime 24894627137 := by
  apply lucas_primality 24894627137 (3 : ZMod 24894627137)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (388978549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (388978549, 1)] : List FactorBlock).map factorBlockValue).prod) = 24894627137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_388978549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 24894627137) ^ 12447313568 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 24894627137) ^ 64 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_25037033243 : Nat.Prime 25037033243 := by
  apply lucas_primality 25037033243 (2 : ZMod 25037033243)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (503, 1), (1914439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (503, 1), (1914439, 1)] : List FactorBlock).map factorBlockValue).prod) = 25037033243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_503
      · exact prime_oneHundredSixteenDJ_1914439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25037033243) ^ 12518516621 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25037033243) ^ 1925925634 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25037033243) ^ 49775414 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25037033243) ^ 13078 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_29838355889 : Nat.Prime 29838355889 := by
  apply lucas_primality 29838355889 (3 : ZMod 29838355889)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (7351, 1), (23063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (7351, 1), (23063, 1)] : List FactorBlock).map factorBlockValue).prod) = 29838355889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_7351
      · exact prime_oneHundredSixteenDJ_23063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29838355889) ^ 14919177944 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 29838355889) ^ 2712577808 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 29838355889) ^ 4059088 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 29838355889) ^ 1293776 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_30435517183 : Nat.Prime 30435517183 := by
  apply lucas_primality 30435517183 (3 : ZMod 30435517183)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (14461, 1), (50111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (14461, 1), (50111, 1)] : List FactorBlock).map factorBlockValue).prod) = 30435517183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_14461
      · exact prime_oneHundredSixteenDJ_50111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30435517183) ^ 15217758591 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30435517183) ^ 10145172394 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30435517183) ^ 4347931026 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30435517183) ^ 2104662 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30435517183) ^ 607362 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_30714515387 : Nat.Prime 30714515387 := by
  apply lucas_primality 30714515387 (2 : ZMod 30714515387)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (194395667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (194395667, 1)] : List FactorBlock).map factorBlockValue).prod) = 30714515387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_79
      · exact prime_oneHundredSixteenDJ_194395667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30714515387) ^ 15357257693 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30714515387) ^ 388791334 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30714515387) ^ 158 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_39138824471 : Nat.Prime 39138824471 := by
  apply lucas_primality 39138824471 (17 : ZMod 39138824471)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (205993813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (205993813, 1)] : List FactorBlock).map factorBlockValue).prod) = 39138824471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_205993813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 39138824471) ^ 19569412235 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (17 : ZMod 39138824471) ^ 7827764894 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (17 : ZMod 39138824471) ^ 2059938130 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (17 : ZMod 39138824471) ^ 190 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_40883621323 : Nat.Prime 40883621323 := by
  apply lucas_primality 40883621323 (2 : ZMod 40883621323)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2621, 1), (2599747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2621, 1), (2599747, 1)] : List FactorBlock).map factorBlockValue).prod) = 40883621323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_2621
      · exact prime_oneHundredSixteenDJ_2599747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40883621323) ^ 20441810661 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40883621323) ^ 13627873774 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40883621323) ^ 15598482 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40883621323) ^ 15726 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_47629402349 : Nat.Prime 47629402349 := by
  apply lucas_primality 47629402349 (2 : ZMod 47629402349)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1082486417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1082486417, 1)] : List FactorBlock).map factorBlockValue).prod) = 47629402349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_1082486417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47629402349) ^ 23814701174 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47629402349) ^ 4329945668 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47629402349) ^ 44 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_51596405131 : Nat.Prime 51596405131 := by
  apply lucas_primality 51596405131 (2 : ZMod 51596405131)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 2), (4764211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 2), (4764211, 1)] : List FactorBlock).map factorBlockValue).prod) = 51596405131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_4764211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51596405131) ^ 25798202565 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51596405131) ^ 17198801710 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51596405131) ^ 10319281026 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51596405131) ^ 2715600270 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51596405131) ^ 10830 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_53082956893 : Nat.Prime 53082956893 := by
  apply lucas_primality 53082956893 (11 : ZMod 53082956893)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (4007, 1), (9277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (4007, 1), (9277, 1)] : List FactorBlock).map factorBlockValue).prod) = 53082956893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_4007
      · exact prime_oneHundredSixteenDJ_9277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 53082956893) ^ 26541478446 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 53082956893) ^ 17694318964 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 53082956893) ^ 7583279556 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 53082956893) ^ 3122526876 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 53082956893) ^ 13247556 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 53082956893) ^ 5721996 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_54105233779 : Nat.Prime 54105233779 := by
  apply lucas_primality 54105233779 (2 : ZMod 54105233779)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (41175977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (41175977, 1)] : List FactorBlock).map factorBlockValue).prod) = 54105233779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_73
      · exact prime_oneHundredSixteenDJ_41175977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54105233779) ^ 27052616889 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54105233779) ^ 18035077926 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54105233779) ^ 741167586 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54105233779) ^ 1314 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_69776322631 : Nat.Prime 69776322631 := by
  apply lucas_primality 69776322631 (7 : ZMod 69776322631)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (383, 1), (867541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (383, 1), (867541, 1)] : List FactorBlock).map factorBlockValue).prod) = 69776322631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_383
      · exact prime_oneHundredSixteenDJ_867541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 69776322631) ^ 34888161315 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 69776322631) ^ 23258774210 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 69776322631) ^ 13955264526 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 69776322631) ^ 9968046090 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 69776322631) ^ 182183610 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 69776322631) ^ 80430 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_72889902937 : Nat.Prime 72889902937 := by
  apply lucas_primality 72889902937 (5 : ZMod 72889902937)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5101, 1), (198463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5101, 1), (198463, 1)] : List FactorBlock).map factorBlockValue).prod) = 72889902937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5101
      · exact prime_oneHundredSixteenDJ_198463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 72889902937) ^ 36444951468 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72889902937) ^ 24296634312 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72889902937) ^ 14289336 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72889902937) ^ 367272 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_98965052167 : Nat.Prime 98965052167 := by
  apply lucas_primality 98965052167 (3 : ZMod 98965052167)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16494175361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16494175361, 1)] : List FactorBlock).map factorBlockValue).prod) = 98965052167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_16494175361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98965052167) ^ 49482526083 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 98965052167) ^ 32988350722 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 98965052167) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_103338683033 : Nat.Prime 103338683033 := by
  apply lucas_primality 103338683033 (3 : ZMod 103338683033)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (993641183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (993641183, 1)] : List FactorBlock).map factorBlockValue).prod) = 103338683033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_993641183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103338683033) ^ 51669341516 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 103338683033) ^ 7949129464 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 103338683033) ^ 104 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_105243810493 : Nat.Prime 105243810493 := by
  apply lucas_primality 105243810493 (5 : ZMod 105243810493)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (367, 1), (23897323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (367, 1), (23897323, 1)] : List FactorBlock).map factorBlockValue).prod) = 105243810493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_367
      · exact prime_oneHundredSixteenDJ_23897323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 105243810493) ^ 52621905246 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 105243810493) ^ 35081270164 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 105243810493) ^ 286767876 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 105243810493) ^ 4404 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_113666263027 : Nat.Prime 113666263027 := by
  apply lucas_primality 113666263027 (2 : ZMod 113666263027)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (611108941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (611108941, 1)] : List FactorBlock).map factorBlockValue).prod) = 113666263027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_31
      · exact prime_oneHundredSixteenDJ_611108941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113666263027) ^ 56833131513 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 113666263027) ^ 37888754342 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 113666263027) ^ 3666653646 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 113666263027) ^ 186 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_159715977601 : Nat.Prime 159715977601 := by
  apply lucas_primality 159715977601 (14 : ZMod 159715977601)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (16637081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (16637081, 1)] : List FactorBlock).map factorBlockValue).prod) = 159715977601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_16637081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 159715977601) ^ 79857988800 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (14 : ZMod 159715977601) ^ 53238659200 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (14 : ZMod 159715977601) ^ 31943195520 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (14 : ZMod 159715977601) ^ 9600 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_167029617749 : Nat.Prime 167029617749 := by
  apply lucas_primality 167029617749 (2 : ZMod 167029617749)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (12043, 1), (495337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (12043, 1), (495337, 1)] : List FactorBlock).map factorBlockValue).prod) = 167029617749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_12043
      · exact prime_oneHundredSixteenDJ_495337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 167029617749) ^ 83514808874 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 167029617749) ^ 23861373964 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 167029617749) ^ 13869436 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 167029617749) ^ 337204 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_184119856867 : Nat.Prime 184119856867 := by
  apply lucas_primality 184119856867 (7 : ZMod 184119856867)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (3041, 1), (101929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (3041, 1), (101929, 1)] : List FactorBlock).map factorBlockValue).prod) = 184119856867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_3041
      · exact prime_oneHundredSixteenDJ_101929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 184119856867) ^ 92059928433 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 184119856867) ^ 61373285622 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 184119856867) ^ 16738168806 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 184119856867) ^ 60545826 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 184119856867) ^ 1806354 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_206582445053 : Nat.Prime 206582445053 := by
  apply lucas_primality 206582445053 (2 : ZMod 206582445053)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (89, 1), (20009923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (89, 1), (20009923, 1)] : List FactorBlock).map factorBlockValue).prod) = 206582445053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_89
      · exact prime_oneHundredSixteenDJ_20009923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 206582445053) ^ 103291222526 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 206582445053) ^ 7123532588 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 206582445053) ^ 2321151068 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 206582445053) ^ 10324 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_288732631151 : Nat.Prime 288732631151 := by
  apply lucas_primality 288732631151 (29 : ZMod 288732631151)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (757, 1), (7628339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (757, 1), (7628339, 1)] : List FactorBlock).map factorBlockValue).prod) = 288732631151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_757
      · exact prime_oneHundredSixteenDJ_7628339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 288732631151) ^ 144366315575 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 288732631151) ^ 57746526230 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 288732631151) ^ 381416950 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 288732631151) ^ 37850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_303164107717 : Nat.Prime 303164107717 := by
  apply lucas_primality 303164107717 (2 : ZMod 303164107717)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (132421, 1), (190783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (132421, 1), (190783, 1)] : List FactorBlock).map factorBlockValue).prod) = 303164107717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_132421
      · exact prime_oneHundredSixteenDJ_190783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 303164107717) ^ 151582053858 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 303164107717) ^ 101054702572 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 303164107717) ^ 2289396 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 303164107717) ^ 1589052 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_368164213771 : Nat.Prime 368164213771 := by
  apply lucas_primality 368164213771 (10 : ZMod 368164213771)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (3011, 1), (99409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (3011, 1), (99409, 1)] : List FactorBlock).map factorBlockValue).prod) = 368164213771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_3011
      · exact prime_oneHundredSixteenDJ_99409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 368164213771) ^ 184082106885 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 368164213771) ^ 122721404590 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 368164213771) ^ 73632842754 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 368164213771) ^ 8979614970 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 368164213771) ^ 122273070 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 368164213771) ^ 3703530 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_417736982447 : Nat.Prime 417736982447 := by
  apply lucas_primality 417736982447 (10 : ZMod 417736982447)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29838355889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29838355889, 1)] : List FactorBlock).map factorBlockValue).prod) = 417736982447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_29838355889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 417736982447) ^ 208868491223 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 417736982447) ^ 59676711778 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 417736982447) ^ 14 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_503278413277 : Nat.Prime 503278413277 := by
  apply lucas_primality 503278413277 (2 : ZMod 503278413277)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (71, 1), (20369047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (71, 1), (20369047, 1)] : List FactorBlock).map factorBlockValue).prod) = 503278413277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_71
      · exact prime_oneHundredSixteenDJ_20369047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 503278413277) ^ 251639206638 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 503278413277) ^ 167759471092 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 503278413277) ^ 17354428044 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 503278413277) ^ 7088428356 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 503278413277) ^ 24708 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_572646669631 : Nat.Prime 572646669631 := by
  apply lucas_primality 572646669631 (6 : ZMod 572646669631)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (239, 1), (265339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (239, 1), (265339, 1)] : List FactorBlock).map factorBlockValue).prod) = 572646669631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_43
      · exact prime_oneHundredSixteenDJ_239
      · exact prime_oneHundredSixteenDJ_265339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 572646669631) ^ 286323334815 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 190882223210 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 114529333926 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 81806667090 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 13317364410 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 2396011170 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 2158170 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_673051521689 : Nat.Prime 673051521689 := by
  apply lucas_primality 673051521689 (3 : ZMod 673051521689)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (10009, 1), (92369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (10009, 1), (92369, 1)] : List FactorBlock).map factorBlockValue).prod) = 673051521689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_10009
      · exact prime_oneHundredSixteenDJ_92369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 673051521689) ^ 336525760844 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 673051521689) ^ 96150217384 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 673051521689) ^ 51773193976 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 673051521689) ^ 67244632 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 673051521689) ^ 7286552 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_982491534593 : Nat.Prime 982491534593 := by
  apply lucas_primality 982491534593 (3 : ZMod 982491534593)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (19, 1), (487, 1), (414769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (19, 1), (487, 1), (414769, 1)] : List FactorBlock).map factorBlockValue).prod) = 982491534593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_487
      · exact prime_oneHundredSixteenDJ_414769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 982491534593) ^ 491245767296 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 982491534593) ^ 51710080768 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 982491534593) ^ 2017436416 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 982491534593) ^ 2368768 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1005248275873 : Nat.Prime 1005248275873 := by
  apply lucas_primality 1005248275873 (5 : ZMod 1005248275873)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (89, 1), (137, 1), (271, 1), (3169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (89, 1), (137, 1), (271, 1), (3169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1005248275873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_89
      · exact prime_oneHundredSixteenDJ_137
      · exact prime_oneHundredSixteenDJ_271
      · exact prime_oneHundredSixteenDJ_3169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1005248275873) ^ 502624137936 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1005248275873) ^ 335082758624 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1005248275873) ^ 11294924448 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1005248275873) ^ 7337578656 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1005248275873) ^ 3709403232 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1005248275873) ^ 317213088 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1180209769019 : Nat.Prime 1180209769019 := by
  apply lucas_primality 1180209769019 (2 : ZMod 1180209769019)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131, 1), (643516777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131, 1), (643516777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180209769019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_131
      · exact prime_oneHundredSixteenDJ_643516777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1180209769019) ^ 590104884509 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180209769019) ^ 168601395574 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180209769019) ^ 9009234878 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180209769019) ^ 1834 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1238476406267 : Nat.Prime 1238476406267 := by
  apply lucas_primality 1238476406267 (2 : ZMod 1238476406267)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (922858723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (922858723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1238476406267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_922858723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1238476406267) ^ 619238203133 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1238476406267) ^ 112588764206 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1238476406267) ^ 20302891906 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1238476406267) ^ 1342 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1964983069187 : Nat.Prime 1964983069187 := by
  apply lucas_primality 1964983069187 (2 : ZMod 1964983069187)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (982491534593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (982491534593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1964983069187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_982491534593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1964983069187) ^ 982491534593 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964983069187) ^ 2 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2258914624817 : Nat.Prime 2258914624817 := by
  apply lucas_primality 2258914624817 (3 : ZMod 2258914624817)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (313, 1), (451061227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (313, 1), (451061227, 1)] : List FactorBlock).map factorBlockValue).prod) = 2258914624817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_313
      · exact prime_oneHundredSixteenDJ_451061227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2258914624817) ^ 1129457312408 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258914624817) ^ 7216979632 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258914624817) ^ 5008 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2368147469641 : Nat.Prime 2368147469641 := by
  apply lucas_primality 2368147469641 (22 : ZMod 2368147469641)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (971, 1), (20323957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (971, 1), (20323957, 1)] : List FactorBlock).map factorBlockValue).prod) = 2368147469641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_971
      · exact prime_oneHundredSixteenDJ_20323957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2368147469641) ^ 1184073734820 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (22 : ZMod 2368147469641) ^ 789382489880 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (22 : ZMod 2368147469641) ^ 473629493928 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (22 : ZMod 2368147469641) ^ 2438874840 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (22 : ZMod 2368147469641) ^ 116520 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2576942583329 : Nat.Prime 2576942583329 := by
  apply lucas_primality 2576942583329 (3 : ZMod 2576942583329)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (1519423693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (1519423693, 1)] : List FactorBlock).map factorBlockValue).prod) = 2576942583329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_53
      · exact prime_oneHundredSixteenDJ_1519423693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2576942583329) ^ 1288471291664 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2576942583329) ^ 48621558176 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2576942583329) ^ 1696 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2620750481123 : Nat.Prime 2620750481123 := by
  apply lucas_primality 2620750481123 (2 : ZMod 2620750481123)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (271, 1), (117934951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (271, 1), (117934951, 1)] : List FactorBlock).map factorBlockValue).prod) = 2620750481123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_271
      · exact prime_oneHundredSixteenDJ_117934951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2620750481123) ^ 1310375240561 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2620750481123) ^ 63920743442 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2620750481123) ^ 9670665982 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2620750481123) ^ 22222 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2941297796699 : Nat.Prime 2941297796699 := by
  apply lucas_primality 2941297796699 (2 : ZMod 2941297796699)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1669, 1), (2689, 1), (327689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1669, 1), (2689, 1), (327689, 1)] : List FactorBlock).map factorBlockValue).prod) = 2941297796699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_1669
      · exact prime_oneHundredSixteenDJ_2689
      · exact prime_oneHundredSixteenDJ_327689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2941297796699) ^ 1470648898349 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2941297796699) ^ 1762311442 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2941297796699) ^ 1093825882 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2941297796699) ^ 8975882 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3570924536941 : Nat.Prime 3570924536941 := by
  apply lucas_primality 3570924536941 (19 : ZMod 3570924536941)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (97, 1), (21157273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (97, 1), (21157273, 1)] : List FactorBlock).map factorBlockValue).prod) = 3570924536941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_97
      · exact prime_oneHundredSixteenDJ_21157273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3570924536941) ^ 1785462268470 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 3570924536941) ^ 1190308178980 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 3570924536941) ^ 714184907388 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 3570924536941) ^ 123135328860 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 3570924536941) ^ 36813655020 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (19 : ZMod 3570924536941) ^ 168780 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_4101304481621 : Nat.Prime 4101304481621 := by
  apply lucas_primality 4101304481621 (2 : ZMod 4101304481621)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (26959, 1), (7606559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (26959, 1), (7606559, 1)] : List FactorBlock).map factorBlockValue).prod) = 4101304481621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_26959
      · exact prime_oneHundredSixteenDJ_7606559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4101304481621) ^ 2050652240810 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4101304481621) ^ 820260896324 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4101304481621) ^ 152131180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4101304481621) ^ 539180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_4271691791749 : Nat.Prime 4271691791749 := by
  apply lucas_primality 4271691791749 (2 : ZMod 4271691791749)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (3259, 1), (4749047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (3259, 1), (4749047, 1)] : List FactorBlock).map factorBlockValue).prod) = 4271691791749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_3259
      · exact prime_oneHundredSixteenDJ_4749047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4271691791749) ^ 2135845895874 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4271691791749) ^ 1423897263916 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4271691791749) ^ 185725730076 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4271691791749) ^ 1310736972 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4271691791749) ^ 899484 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_4957978681273 : Nat.Prime 4957978681273 := by
  apply lucas_primality 4957978681273 (5 : ZMod 4957978681273)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (206582445053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (206582445053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4957978681273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_206582445053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4957978681273) ^ 2478989340636 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4957978681273) ^ 1652659560424 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4957978681273) ^ 24 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5583213862823 : Nat.Prime 5583213862823 := by
  apply lucas_primality 5583213862823 (5 : ZMod 5583213862823)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (727, 1), (1279, 1), (1667, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (727, 1), (1279, 1), (1667, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) = 5583213862823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_727
      · exact prime_oneHundredSixteenDJ_1279
      · exact prime_oneHundredSixteenDJ_1667
      · exact prime_oneHundredSixteenDJ_1801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5583213862823) ^ 2791606931411 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5583213862823) ^ 7679798986 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5583213862823) ^ 4365296218 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5583213862823) ^ 3349258466 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5583213862823) ^ 3100063222 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5655103262251 : Nat.Prime 5655103262251 := by
  apply lucas_primality 5655103262251 (10 : ZMod 5655103262251)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (13, 1), (587, 1), (988093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (13, 1), (587, 1), (988093, 1)] : List FactorBlock).map factorBlockValue).prod) = 5655103262251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_587
      · exact prime_oneHundredSixteenDJ_988093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5655103262251) ^ 2827551631125 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5655103262251) ^ 1885034420750 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5655103262251) ^ 1131020652450 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5655103262251) ^ 435007943250 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5655103262251) ^ 9633906750 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5655103262251) ^ 5723250 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_6043339160951 : Nat.Prime 6043339160951 := by
  apply lucas_primality 6043339160951 (11 : ZMod 6043339160951)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (13, 1), (29, 1), (251, 1), (182471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (13, 1), (29, 1), (251, 1), (182471, 1)] : List FactorBlock).map factorBlockValue).prod) = 6043339160951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_251
      · exact prime_oneHundredSixteenDJ_182471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6043339160951) ^ 3021669580475 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6043339160951) ^ 1208667832190 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6043339160951) ^ 863334165850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6043339160951) ^ 464872243150 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6043339160951) ^ 208391005550 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6043339160951) ^ 24077048450 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6043339160951) ^ 33119450 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_6124078275703 : Nat.Prime 6124078275703 := by
  apply lucas_primality 6124078275703 (3 : ZMod 6124078275703)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (24894627137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (24894627137, 1)] : List FactorBlock).map factorBlockValue).prod) = 6124078275703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_24894627137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6124078275703) ^ 3062039137851 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6124078275703) ^ 2041359425234 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6124078275703) ^ 149367762822 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6124078275703) ^ 246 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_10688651354677 : Nat.Prime 10688651354677 := by
  apply lucas_primality 10688651354677 (5 : ZMod 10688651354677)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (30714515387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (30714515387, 1)] : List FactorBlock).map factorBlockValue).prod) = 10688651354677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_30714515387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10688651354677) ^ 5344325677338 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 10688651354677) ^ 3562883784892 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 10688651354677) ^ 368574184644 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 10688651354677) ^ 348 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_11288601358633 : Nat.Prime 11288601358633 := by
  apply lucas_primality 11288601358633 (5 : ZMod 11288601358633)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (13, 1), (1049, 1), (425819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (13, 1), (1049, 1), (425819, 1)] : List FactorBlock).map factorBlockValue).prod) = 11288601358633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_1049
      · exact prime_oneHundredSixteenDJ_425819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11288601358633) ^ 5644300679316 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11288601358633) ^ 3762867119544 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11288601358633) ^ 868353950664 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11288601358633) ^ 10761297768 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11288601358633) ^ 26510328 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_11795706684821 : Nat.Prime 11795706684821 := by
  apply lucas_primality 11795706684821 (2 : ZMod 11795706684821)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (34327, 1), (17181383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (34327, 1), (17181383, 1)] : List FactorBlock).map factorBlockValue).prod) = 11795706684821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_34327
      · exact prime_oneHundredSixteenDJ_17181383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11795706684821) ^ 5897853342410 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11795706684821) ^ 2359141336964 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11795706684821) ^ 343627660 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11795706684821) ^ 686540 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_12103373607107 : Nat.Prime 12103373607107 := by
  apply lucas_primality 12103373607107 (2 : ZMod 12103373607107)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (811, 1), (7462005923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (811, 1), (7462005923, 1)] : List FactorBlock).map factorBlockValue).prod) = 12103373607107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_811
      · exact prime_oneHundredSixteenDJ_7462005923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12103373607107) ^ 6051686803553 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 12103373607107) ^ 14924011846 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 12103373607107) ^ 1622 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_17053741643647 : Nat.Prime 17053741643647 := by
  apply lucas_primality 17053741643647 (3 : ZMod 17053741643647)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (415409, 1), (6842149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (415409, 1), (6842149, 1)] : List FactorBlock).map factorBlockValue).prod) = 17053741643647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_415409
      · exact prime_oneHundredSixteenDJ_6842149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17053741643647) ^ 8526870821823 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17053741643647) ^ 5684580547882 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17053741643647) ^ 41052894 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17053741643647) ^ 2492454 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_19971833404739 : Nat.Prime 19971833404739 := by
  apply lucas_primality 19971833404739 (2 : ZMod 19971833404739)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (72889902937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (72889902937, 1)] : List FactorBlock).map factorBlockValue).prod) = 19971833404739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_137
      · exact prime_oneHundredSixteenDJ_72889902937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19971833404739) ^ 9985916702369 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19971833404739) ^ 145779805874 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19971833404739) ^ 274 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_20129035334069 : Nat.Prime 20129035334069 := by
  apply lucas_primality 20129035334069 (2 : ZMod 20129035334069)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (29, 1), (79613, 1), (128213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (29, 1), (79613, 1), (128213, 1)] : List FactorBlock).map factorBlockValue).prod) = 20129035334069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_79613
      · exact prime_oneHundredSixteenDJ_128213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20129035334069) ^ 10064517667034 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 1184060902004 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 694104666692 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 252836036 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 156996836 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_22831969868053 : Nat.Prime 22831969868053 := by
  apply lucas_primality 22831969868053 (2 : ZMod 22831969868053)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (8308577099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (8308577099, 1)] : List FactorBlock).map factorBlockValue).prod) = 22831969868053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_229
      · exact prime_oneHundredSixteenDJ_8308577099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22831969868053) ^ 11415984934026 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22831969868053) ^ 7610656622684 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22831969868053) ^ 99702925188 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22831969868053) ^ 2748 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_23790185938483 : Nat.Prime 23790185938483 := by
  apply lucas_primality 23790185938483 (2 : ZMod 23790185938483)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (79, 1), (9521, 1), (181777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (79, 1), (9521, 1), (181777, 1)] : List FactorBlock).map factorBlockValue).prod) = 23790185938483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_79
      · exact prime_oneHundredSixteenDJ_9521
      · exact prime_oneHundredSixteenDJ_181777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23790185938483) ^ 11895092969241 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23790185938483) ^ 7930061979494 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23790185938483) ^ 820351239258 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23790185938483) ^ 301141594158 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23790185938483) ^ 2498706642 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23790185938483) ^ 130875666 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_27824990649587 : Nat.Prime 27824990649587 := by
  apply lucas_primality 27824990649587 (2 : ZMod 27824990649587)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (503, 1), (125154011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (503, 1), (125154011, 1)] : List FactorBlock).map factorBlockValue).prod) = 27824990649587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_503
      · exact prime_oneHundredSixteenDJ_125154011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27824990649587) ^ 13912495324793 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 2140383896122 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 1636764155858 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 55318072862 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 222326 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_30800743389197 : Nat.Prime 30800743389197 := by
  apply lucas_primality 30800743389197 (3 : ZMod 30800743389197)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (30435517183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (30435517183, 1)] : List FactorBlock).map factorBlockValue).prod) = 30800743389197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_30435517183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30800743389197) ^ 15400371694598 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800743389197) ^ 2800067580836 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800743389197) ^ 1339162756052 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800743389197) ^ 1012 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_31989492017311 : Nat.Prime 31989492017311 := by
  apply lucas_primality 31989492017311 (12 : ZMod 31989492017311)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (22687582991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (22687582991, 1)] : List FactorBlock).map factorBlockValue).prod) = 31989492017311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_47
      · exact prime_oneHundredSixteenDJ_22687582991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 31989492017311) ^ 15994746008655 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 31989492017311) ^ 10663164005770 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 31989492017311) ^ 6397898403462 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 31989492017311) ^ 680627489730 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 31989492017311) ^ 1410 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_37789624941161 : Nat.Prime 37789624941161 := by
  apply lucas_primality 37789624941161 (3 : ZMod 37789624941161)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (97, 1), (2837, 1), (3433061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (97, 1), (2837, 1), (3433061, 1)] : List FactorBlock).map factorBlockValue).prod) = 37789624941161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_97
      · exact prime_oneHundredSixteenDJ_2837
      · exact prime_oneHundredSixteenDJ_3433061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37789624941161) ^ 18894812470580 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37789624941161) ^ 7557924988232 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37789624941161) ^ 389583762280 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37789624941161) ^ 13320276680 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37789624941161) ^ 11007560 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_40807927643893 : Nat.Prime 40807927643893 := by
  apply lucas_primality 40807927643893 (2 : ZMod 40807927643893)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (281839, 1), (635051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (281839, 1), (635051, 1)] : List FactorBlock).map factorBlockValue).prod) = 40807927643893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_281839
      · exact prime_oneHundredSixteenDJ_635051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40807927643893) ^ 20403963821946 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40807927643893) ^ 13602642547964 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40807927643893) ^ 2147785665468 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40807927643893) ^ 144791628 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40807927643893) ^ 64259292 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_44012503326523 : Nat.Prime 44012503326523 := by
  apply lucas_primality 44012503326523 (3 : ZMod 44012503326523)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9323, 1), (786808669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9323, 1), (786808669, 1)] : List FactorBlock).map factorBlockValue).prod) = 44012503326523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_9323
      · exact prime_oneHundredSixteenDJ_786808669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44012503326523) ^ 22006251663261 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 44012503326523) ^ 14670834442174 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 44012503326523) ^ 4720852014 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 44012503326523) ^ 55938 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_61802817949039 : Nat.Prime 61802817949039 := by
  apply lucas_primality 61802817949039 (3 : ZMod 61802817949039)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (503, 1), (20478070891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (503, 1), (20478070891, 1)] : List FactorBlock).map factorBlockValue).prod) = 61802817949039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_503
      · exact prime_oneHundredSixteenDJ_20478070891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61802817949039) ^ 30901408974519 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 61802817949039) ^ 20600939316346 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 61802817949039) ^ 122868425346 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 61802817949039) ^ 3018 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_101807112487879 : Nat.Prime 101807112487879 := by
  apply lucas_primality 101807112487879 (6 : ZMod 101807112487879)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (73, 1), (433, 1), (3651731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (73, 1), (433, 1), (3651731, 1)] : List FactorBlock).map factorBlockValue).prod) = 101807112487879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_73
      · exact prime_oneHundredSixteenDJ_433
      · exact prime_oneHundredSixteenDJ_3651731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 101807112487879) ^ 50903556243939 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 101807112487879) ^ 33935704162626 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 101807112487879) ^ 14543873212554 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 101807112487879) ^ 1394617979286 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 101807112487879) ^ 235120352166 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 101807112487879) ^ 27879138 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_192832978518113 : Nat.Prime 192832978518113 := by
  apply lucas_primality 192832978518113 (3 : ZMod 192832978518113)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (673429, 1), (8948279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (673429, 1), (8948279, 1)] : List FactorBlock).map factorBlockValue).prod) = 192832978518113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_673429
      · exact prime_oneHundredSixteenDJ_8948279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 192832978518113) ^ 96416489259056 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 192832978518113) ^ 286344928 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 192832978518113) ^ 21549728 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_246405947113577 : Nat.Prime 246405947113577 := by
  apply lucas_primality 246405947113577 (3 : ZMod 246405947113577)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (30800743389197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (30800743389197, 1)] : List FactorBlock).map factorBlockValue).prod) = 246405947113577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_30800743389197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 246405947113577) ^ 123202973556788 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 246405947113577) ^ 8 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_10789
      · exact prime_oneHundredSixteenDJ_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_290904508172549 : Nat.Prime 290904508172549 := by
  apply lucas_primality 290904508172549 (2 : ZMod 290904508172549)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (572646669631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (572646669631, 1)] : List FactorBlock).map factorBlockValue).prod) = 290904508172549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_127
      · exact prime_oneHundredSixteenDJ_572646669631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290904508172549) ^ 145452254086274 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 290904508172549) ^ 2290586678524 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 290904508172549) ^ 508 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_301801776835063 : Nat.Prime 301801776835063 := by
  apply lucas_primality 301801776835063 (5 : ZMod 301801776835063)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (47, 1), (24977, 1), (165437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (47, 1), (24977, 1), (165437, 1)] : List FactorBlock).map factorBlockValue).prod) = 301801776835063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_37
      · exact prime_oneHundredSixteenDJ_47
      · exact prime_oneHundredSixteenDJ_24977
      · exact prime_oneHundredSixteenDJ_165437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 301801776835063) ^ 150900888417531 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 301801776835063) ^ 100600592278354 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 301801776835063) ^ 43114539547866 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 301801776835063) ^ 8156804779326 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 301801776835063) ^ 6421314400746 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 301801776835063) ^ 12083187606 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 301801776835063) ^ 1824270126 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_316877884485823 : Nat.Prime 316877884485823 := by
  apply lucas_primality 316877884485823 (3 : ZMod 316877884485823)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1453, 1), (1101440713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1453, 1), (1101440713, 1)] : List FactorBlock).map factorBlockValue).prod) = 316877884485823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_1453
      · exact prime_oneHundredSixteenDJ_1101440713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 316877884485823) ^ 158438942242911 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 105625961495274 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 28807080407802 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 218085261174 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 287694 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_685576022919041 : Nat.Prime 685576022919041 := by
  apply lucas_primality 685576022919041 (3 : ZMod 685576022919041)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (11, 1), (101, 1), (964187701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (11, 1), (101, 1), (964187701, 1)] : List FactorBlock).map factorBlockValue).prod) = 685576022919041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_101
      · exact prime_oneHundredSixteenDJ_964187701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 685576022919041) ^ 342788011459520 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 685576022919041) ^ 137115204583808 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 685576022919041) ^ 62325092992640 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 685576022919041) ^ 6787881415040 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 685576022919041) ^ 711040 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_857623899386777 : Nat.Prime 857623899386777 := by
  apply lucas_primality 857623899386777 (3 : ZMod 857623899386777)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (619, 1), (34649, 1), (217319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (619, 1), (34649, 1), (217319, 1)] : List FactorBlock).map factorBlockValue).prod) = 857623899386777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_619
      · exact prime_oneHundredSixteenDJ_34649
      · exact prime_oneHundredSixteenDJ_217319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 857623899386777) ^ 428811949693388 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 857623899386777) ^ 37287995625512 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 857623899386777) ^ 1385499029704 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 857623899386777) ^ 24751764824 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 857623899386777) ^ 3946382504 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1061128527711503 : Nat.Prime 1061128527711503 := by
  apply lucas_primality 1061128527711503 (5 : ZMod 1061128527711503)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (11288601358633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (11288601358633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1061128527711503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_47
      · exact prime_oneHundredSixteenDJ_11288601358633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1061128527711503) ^ 530564263855751 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1061128527711503) ^ 22577202717266 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1061128527711503) ^ 94 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1119710445925699 : Nat.Prime 1119710445925699 := by
  apply lucas_primality 1119710445925699 (2 : ZMod 1119710445925699)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (5655103262251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (5655103262251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1119710445925699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_5655103262251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1119710445925699) ^ 559855222962849 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119710445925699) ^ 373236815308566 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119710445925699) ^ 101791858720518 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119710445925699) ^ 198 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1856303979439153 : Nat.Prime 1856303979439153 := by
  apply lucas_primality 1856303979439153 (5 : ZMod 1856303979439153)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (59, 1), (389, 1), (1685024599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (59, 1), (389, 1), (1685024599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1856303979439153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_59
      · exact prime_oneHundredSixteenDJ_389
      · exact prime_oneHundredSixteenDJ_1685024599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1856303979439153) ^ 928151989719576 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1856303979439153) ^ 618767993146384 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1856303979439153) ^ 31462779312528 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1856303979439153) ^ 4771989664368 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1856303979439153) ^ 1101648 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2977166017181567 : Nat.Prime 2977166017181567 := by
  apply lucas_primality 2977166017181567 (5 : ZMod 2977166017181567)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (647, 1), (1597, 1), (10832089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (647, 1), (1597, 1), (10832089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2977166017181567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_647
      · exact prime_oneHundredSixteenDJ_1597
      · exact prime_oneHundredSixteenDJ_10832089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2977166017181567) ^ 1488583008590783 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2977166017181567) ^ 425309431025938 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2977166017181567) ^ 156692948272714 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2977166017181567) ^ 4601493071378 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2977166017181567) ^ 1864224181078 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2977166017181567) ^ 274846894 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3143950669812857 : Nat.Prime 3143950669812857 := by
  apply lucas_primality 3143950669812857 (3 : ZMod 3143950669812857)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (619, 1), (1123, 1), (565347311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (619, 1), (1123, 1), (565347311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3143950669812857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_619
      · exact prime_oneHundredSixteenDJ_1123
      · exact prime_oneHundredSixteenDJ_565347311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3143950669812857) ^ 1571975334906428 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3143950669812857) ^ 5079080242024 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3143950669812857) ^ 2799599884072 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3143950669812857) ^ 5561096 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_4429408840150681 : Nat.Prime 4429408840150681 := by
  apply lucas_primality 4429408840150681 (17 : ZMod 4429408840150681)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (4101304481621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (4101304481621, 1)] : List FactorBlock).map factorBlockValue).prod) = 4429408840150681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_4101304481621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 4429408840150681) ^ 2214704420075340 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (17 : ZMod 4429408840150681) ^ 1476469613383560 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (17 : ZMod 4429408840150681) ^ 885881768030136 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (17 : ZMod 4429408840150681) ^ 1080 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_4435307048044387 : Nat.Prime 4435307048044387 := by
  apply lucas_primality 4435307048044387 (2 : ZMod 4435307048044387)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (246405947113577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (246405947113577, 1)] : List FactorBlock).map factorBlockValue).prod) = 4435307048044387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_246405947113577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4435307048044387) ^ 2217653524022193 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4435307048044387) ^ 1478435682681462 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4435307048044387) ^ 18 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5852768765443141 : Nat.Prime 5852768765443141 := by
  apply lucas_primality 5852768765443141 (2 : ZMod 5852768765443141)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (41479, 1), (102247807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (41479, 1), (102247807, 1)] : List FactorBlock).map factorBlockValue).prod) = 5852768765443141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_41479
      · exact prime_oneHundredSixteenDJ_102247807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5852768765443141) ^ 2926384382721570 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5852768765443141) ^ 1950922921814380 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5852768765443141) ^ 1170553753088628 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5852768765443141) ^ 254468207193180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5852768765443141) ^ 141101973660 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5852768765443141) ^ 57241020 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_8523242221328741 : Nat.Prime 8523242221328741 := by
  apply lucas_primality 8523242221328741 (2 : ZMod 8523242221328741)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (9857, 1), (9949, 1), (4345609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (9857, 1), (9949, 1), (4345609, 1)] : List FactorBlock).map factorBlockValue).prod) = 8523242221328741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_9857
      · exact prime_oneHundredSixteenDJ_9949
      · exact prime_oneHundredSixteenDJ_4345609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8523242221328741) ^ 4261621110664370 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8523242221328741) ^ 1704648444265748 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8523242221328741) ^ 864689278820 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8523242221328741) ^ 856693358260 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8523242221328741) ^ 1961345860 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_9889213193728541 : Nat.Prime 9889213193728541 := by
  apply lucas_primality 9889213193728541 (12 : ZMod 9889213193728541)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (233, 1), (303164107717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (233, 1), (303164107717, 1)] : List FactorBlock).map factorBlockValue).prod) = 9889213193728541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_233
      · exact prime_oneHundredSixteenDJ_303164107717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 9889213193728541) ^ 4944606596864270 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 1977842638745708 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 1412744741961220 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 42442975080380 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 32620 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_11994594132657967 : Nat.Prime 11994594132657967 := by
  apply lucas_primality 11994594132657967 (3 : ZMod 11994594132657967)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (941609, 1), (2123067029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (941609, 1), (2123067029, 1)] : List FactorBlock).map factorBlockValue).prod) = 11994594132657967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_941609
      · exact prime_oneHundredSixteenDJ_2123067029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11994594132657967) ^ 5997297066328983 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11994594132657967) ^ 3998198044219322 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11994594132657967) ^ 12738402174 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11994594132657967) ^ 5649654 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_17101842167483201 : Nat.Prime 17101842167483201 := by
  apply lucas_primality 17101842167483201 (3 : ZMod 17101842167483201)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (10688651354677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (10688651354677, 1)] : List FactorBlock).map factorBlockValue).prod) = 17101842167483201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_10688651354677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17101842167483201) ^ 8550921083741600 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17101842167483201) ^ 3420368433496640 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17101842167483201) ^ 1600 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_19315313717444033 : Nat.Prime 19315313717444033 := by
  apply lucas_primality 19315313717444033 (3 : ZMod 19315313717444033)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (301801776835063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (301801776835063, 1)] : List FactorBlock).map factorBlockValue).prod) = 19315313717444033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_301801776835063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 19315313717444033) ^ 9657656858722016 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 19315313717444033) ^ 64 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_35116612592658847 : Nat.Prime 35116612592658847 := by
  apply lucas_primality 35116612592658847 (3 : ZMod 35116612592658847)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5852768765443141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5852768765443141, 1)] : List FactorBlock).map factorBlockValue).prod) = 35116612592658847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5852768765443141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35116612592658847) ^ 17558306296329423 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35116612592658847) ^ 11705537530886282 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35116612592658847) ^ 6 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_46732220409796457 : Nat.Prime 46732220409796457 := by
  apply lucas_primality 46732220409796457 (3 : ZMod 46732220409796457)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (31, 1), (554633, 1), (17881561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (31, 1), (554633, 1), (17881561, 1)] : List FactorBlock).map factorBlockValue).prod) = 46732220409796457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_31
      · exact prime_oneHundredSixteenDJ_554633
      · exact prime_oneHundredSixteenDJ_17881561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46732220409796457) ^ 23366110204898228 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46732220409796457) ^ 2459590547884024 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46732220409796457) ^ 1507490980961176 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46732220409796457) ^ 84257915432 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46732220409796457) ^ 2613430696 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_49101347063840257 : Nat.Prime 49101347063840257 := by
  apply lucas_primality 49101347063840257 (5 : ZMod 49101347063840257)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (106963, 1), (99620189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (106963, 1), (99620189, 1)] : List FactorBlock).map factorBlockValue).prod) = 49101347063840257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_106963
      · exact prime_oneHundredSixteenDJ_99620189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 49101347063840257) ^ 24550673531920128 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49101347063840257) ^ 16367115687946752 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49101347063840257) ^ 459049830912 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 49101347063840257) ^ 492885504 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_78303288274877279 : Nat.Prime 78303288274877279 := by
  apply lucas_primality 78303288274877279 (11 : ZMod 78303288274877279)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (188767, 1), (120796301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (188767, 1), (120796301, 1)] : List FactorBlock).map factorBlockValue).prod) = 78303288274877279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_101
      · exact prime_oneHundredSixteenDJ_188767
      · exact prime_oneHundredSixteenDJ_120796301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 78303288274877279) ^ 39151644137438639 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 4606075780875134 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 775280081929478 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 414814497634 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 648225878 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_140940615619369207 : Nat.Prime 140940615619369207 := by
  apply lucas_primality 140940615619369207 (3 : ZMod 140940615619369207)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (3753137, 1), (77269033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (3753137, 1), (77269033, 1)] : List FactorBlock).map factorBlockValue).prod) = 140940615619369207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_3753137
      · exact prime_oneHundredSixteenDJ_77269033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 140940615619369207) ^ 70470307809684603 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 140940615619369207) ^ 46980205206456402 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 140940615619369207) ^ 37552750038 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 140940615619369207) ^ 1824024582 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_153697439591436319 : Nat.Prime 153697439591436319 := by
  apply lucas_primality 153697439591436319 (3 : ZMod 153697439591436319)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (197, 1), (104779, 1), (8328919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (197, 1), (104779, 1), (8328919, 1)] : List FactorBlock).map factorBlockValue).prod) = 153697439591436319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_149
      · exact prime_oneHundredSixteenDJ_197
      · exact prime_oneHundredSixteenDJ_104779
      · exact prime_oneHundredSixteenDJ_8328919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 153697439591436319) ^ 76848719795718159 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153697439591436319) ^ 51232479863812106 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153697439591436319) ^ 1031526440210982 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153697439591436319) ^ 780190048687494 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153697439591436319) ^ 1466872556442 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 153697439591436319) ^ 18453467922 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_223631459441802673 : Nat.Prime 223631459441802673 := by
  apply lucas_primality 223631459441802673 (5 : ZMod 223631459441802673)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (14249, 1), (83761, 1), (300277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (14249, 1), (83761, 1), (300277, 1)] : List FactorBlock).map factorBlockValue).prod) = 223631459441802673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_14249
      · exact prime_oneHundredSixteenDJ_83761
      · exact prime_oneHundredSixteenDJ_300277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 223631459441802673) ^ 111815729720901336 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 223631459441802673) ^ 74543819813934224 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 223631459441802673) ^ 17202419957061744 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 223631459441802673) ^ 15694537121328 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 223631459441802673) ^ 2669875711152 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 223631459441802673) ^ 744750545136 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_229662409153464871 : Nat.Prime 229662409153464871 := by
  apply lucas_primality 229662409153464871 (11 : ZMod 229662409153464871)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (11795706684821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (11795706684821, 1)] : List FactorBlock).map factorBlockValue).prod) = 229662409153464871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_59
      · exact prime_oneHundredSixteenDJ_11795706684821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 229662409153464871) ^ 114831204576732435 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 76554136384488290 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 45932481830692974 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 20878400832133170 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 3892583205990930 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 19470 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_356794724615209037 : Nat.Prime 356794724615209037 := by
  apply lucas_primality 356794724615209037 (2 : ZMod 356794724615209037)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (839, 1), (6451, 1), (1267727987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (839, 1), (6451, 1), (1267727987, 1)] : List FactorBlock).map factorBlockValue).prod) = 356794724615209037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_839
      · exact prime_oneHundredSixteenDJ_6451
      · exact prime_oneHundredSixteenDJ_1267727987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 356794724615209037) ^ 178397362307604518 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 27445748047323772 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 425261888695124 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 55308436616836 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 281444228 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_379038915230881987 : Nat.Prime 379038915230881987 := by
  apply lucas_primality 379038915230881987 (2 : ZMod 379038915230881987)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (73883, 1), (273473, 1), (347401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (73883, 1), (273473, 1), (347401, 1)] : List FactorBlock).map factorBlockValue).prod) = 379038915230881987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_73883
      · exact prime_oneHundredSixteenDJ_273473
      · exact prime_oneHundredSixteenDJ_347401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 379038915230881987) ^ 189519457615440993 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 379038915230881987) ^ 126346305076960662 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 379038915230881987) ^ 5130258858342 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 379038915230881987) ^ 1386019516482 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 379038915230881987) ^ 1091070305586 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_529458955499661463 : Nat.Prime 529458955499661463 := by
  apply lucas_primality 529458955499661463 (3 : ZMod 529458955499661463)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (761377, 1), (1170701299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (761377, 1), (1170701299, 1)] : List FactorBlock).map factorBlockValue).prod) = 529458955499661463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_761377
      · exact prime_oneHundredSixteenDJ_1170701299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 529458955499661463) ^ 264729477749830731 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529458955499661463) ^ 176486318499887154 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529458955499661463) ^ 48132632318151042 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529458955499661463) ^ 695396571606 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529458955499661463) ^ 452257938 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_594249353923685191 : Nat.Prime 594249353923685191 := by
  apply lucas_primality 594249353923685191 (3 : ZMod 594249353923685191)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (16699, 1), (69776322631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (16699, 1), (69776322631, 1)] : List FactorBlock).map factorBlockValue).prod) = 594249353923685191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_16699
      · exact prime_oneHundredSixteenDJ_69776322631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 594249353923685191) ^ 297124676961842595 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 594249353923685191) ^ 198083117974561730 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 594249353923685191) ^ 118849870784737038 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 594249353923685191) ^ 34955844348452070 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 594249353923685191) ^ 35585924541810 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 594249353923685191) ^ 8516490 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_632926437747441427 : Nat.Prime 632926437747441427 := by
  apply lucas_primality 632926437747441427 (2 : ZMod 632926437747441427)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (857623899386777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (857623899386777, 1)] : List FactorBlock).map factorBlockValue).prod) = 632926437747441427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_857623899386777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 632926437747441427) ^ 316463218873720713 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 632926437747441427) ^ 210975479249147142 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 632926437747441427) ^ 15437230188961986 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 632926437747441427) ^ 738 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_704476277925837371 : Nat.Prime 704476277925837371 := by
  apply lucas_primality 704476277925837371 (2 : ZMod 704476277925837371)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (37, 1), (61, 1), (997, 1), (1079547257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (37, 1), (61, 1), (997, 1), (1079547257, 1)] : List FactorBlock).map factorBlockValue).prod) = 704476277925837371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_37
      · exact prime_oneHundredSixteenDJ_61
      · exact prime_oneHundredSixteenDJ_997
      · exact prime_oneHundredSixteenDJ_1079547257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 704476277925837371) ^ 352238138962918685 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 140895255585167474 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 24292285445718530 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 19039899403401010 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 11548791441407170 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 706596066124210 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 652566410 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_934644408195929141 : Nat.Prime 934644408195929141 := by
  apply lucas_primality 934644408195929141 (3 : ZMod 934644408195929141)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (46732220409796457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (46732220409796457, 1)] : List FactorBlock).map factorBlockValue).prod) = 934644408195929141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_46732220409796457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 934644408195929141) ^ 467322204097964570 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 934644408195929141) ^ 186928881639185828 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 934644408195929141) ^ 20 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_985678153211136269 : Nat.Prime 985678153211136269 := by
  apply lucas_primality 985678153211136269 (2 : ZMod 985678153211136269)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (16061, 1), (1180209769019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (16061, 1), (1180209769019, 1)] : List FactorBlock).map factorBlockValue).prod) = 985678153211136269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_16061
      · exact prime_oneHundredSixteenDJ_1180209769019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 985678153211136269) ^ 492839076605568134 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 985678153211136269) ^ 75821396400856636 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 985678153211136269) ^ 61370907988988 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 985678153211136269) ^ 835172 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1184189576153641879 : Nat.Prime 1184189576153641879 := by
  apply lucas_primality 1184189576153641879 (6 : ZMod 1184189576153641879)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (151, 1), (15187, 1), (117734479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (151, 1), (15187, 1), (117734479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184189576153641879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_43
      · exact prime_oneHundredSixteenDJ_151
      · exact prime_oneHundredSixteenDJ_15187
      · exact prime_oneHundredSixteenDJ_117734479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1184189576153641879) ^ 592094788076820939 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1184189576153641879) ^ 394729858717880626 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1184189576153641879) ^ 69658210361978934 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1184189576153641879) ^ 27539292468689346 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1184189576153641879) ^ 7842315073865178 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1184189576153641879) ^ 77973897158994 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1184189576153641879) ^ 10058137482 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_101
      · exact prime_oneHundredSixteenDJ_191
      · exact prime_oneHundredSixteenDJ_48017
      · exact prime_oneHundredSixteenDJ_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2483429385636445577 : Nat.Prime 2483429385636445577 := by
  apply lucas_primality 2483429385636445577 (6 : ZMod 2483429385636445577)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (3313, 1), (15607, 1), (545793397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (3313, 1), (15607, 1), (545793397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2483429385636445577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_3313
      · exact prime_oneHundredSixteenDJ_15607
      · exact prime_oneHundredSixteenDJ_545793397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2483429385636445577) ^ 1241714692818222788 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 225766307785131416 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 749601384134152 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 159122790134968 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 4550127208 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3780048129433800569 : Nat.Prime 3780048129433800569 := by
  apply lucas_primality 3780048129433800569 (3 : ZMod 3780048129433800569)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (173, 1), (15913, 1), (5918493551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (173, 1), (15913, 1), (5918493551, 1)] : List FactorBlock).map factorBlockValue).prod) = 3780048129433800569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_173
      · exact prime_oneHundredSixteenDJ_15913
      · exact prime_oneHundredSixteenDJ_5918493551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3780048129433800569) ^ 1890024064716900284 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3780048129433800569) ^ 130346487221855192 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3780048129433800569) ^ 21849989187478616 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3780048129433800569) ^ 237544657162936 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3780048129433800569) ^ 638684168 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_6006028065928376153 : Nat.Prime 6006028065928376153 := by
  apply lucas_primality 6006028065928376153 (3 : ZMod 6006028065928376153)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3863, 1), (25349, 1), (7666759337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3863, 1), (25349, 1), (7666759337, 1)] : List FactorBlock).map factorBlockValue).prod) = 6006028065928376153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3863
      · exact prime_oneHundredSixteenDJ_25349
      · exact prime_oneHundredSixteenDJ_7666759337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6006028065928376153) ^ 3003014032964188076 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6006028065928376153) ^ 1554757459468904 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6006028065928376153) ^ 236933530550648 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6006028065928376153) ^ 783385496 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_17874937826682975139 : Nat.Prime 17874937826682975139 := by
  apply lucas_primality 17874937826682975139 (2 : ZMod 17874937826682975139)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89627, 1), (321721, 1), (103317769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89627, 1), (321721, 1), (103317769, 1)] : List FactorBlock).map factorBlockValue).prod) = 17874937826682975139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_89627
      · exact prime_oneHundredSixteenDJ_321721
      · exact prime_oneHundredSixteenDJ_103317769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17874937826682975139) ^ 8937468913341487569 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17874937826682975139) ^ 5958312608894325046 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17874937826682975139) ^ 199436975762694 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17874937826682975139) ^ 55560370092978 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17874937826682975139) ^ 173009328402 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_27443920666759854769 : Nat.Prime 27443920666759854769 := by
  apply lucas_primality 27443920666759854769 (13 : ZMod 27443920666759854769)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (73951, 1), (368164213771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (73951, 1), (368164213771, 1)] : List FactorBlock).map factorBlockValue).prod) = 27443920666759854769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_73951
      · exact prime_oneHundredSixteenDJ_368164213771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 27443920666759854769) ^ 13721960333379927384 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 27443920666759854769) ^ 9147973555586618256 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 27443920666759854769) ^ 3920560095251407824 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 27443920666759854769) ^ 371109527481168 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (13 : ZMod 27443920666759854769) ^ 74542608 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_29002215117025636943 : Nat.Prime 29002215117025636943 := by
  apply lucas_primality 29002215117025636943 (5 : ZMod 29002215117025636943)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19381, 1), (44012503326523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19381, 1), (44012503326523, 1)] : List FactorBlock).map factorBlockValue).prod) = 29002215117025636943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_19381
      · exact prime_oneHundredSixteenDJ_44012503326523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29002215117025636943) ^ 14501107558512818471 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29002215117025636943) ^ 1706012653942684526 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29002215117025636943) ^ 1496425113101782 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29002215117025636943) ^ 658954 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_55229416789943417137 : Nat.Prime 55229416789943417137 := by
  apply lucas_primality 55229416789943417137 (5 : ZMod 55229416789943417137)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (21675749, 1), (53082956893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (21675749, 1), (53082956893, 1)] : List FactorBlock).map factorBlockValue).prod) = 55229416789943417137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_21675749
      · exact prime_oneHundredSixteenDJ_53082956893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 55229416789943417137) ^ 27614708394971708568 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 55229416789943417137) ^ 18409805596647805712 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 55229416789943417137) ^ 2547981930864 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 55229416789943417137) ^ 1040435952 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_58004430234051273887 : Nat.Prime 58004430234051273887 := by
  apply lucas_primality 58004430234051273887 (5 : ZMod 58004430234051273887)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29002215117025636943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29002215117025636943, 1)] : List FactorBlock).map factorBlockValue).prod) = 58004430234051273887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_29002215117025636943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 58004430234051273887) ^ 29002215117025636943 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 58004430234051273887) ^ 2 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_78781488676897957459 : Nat.Prime 78781488676897957459 := by
  apply lucas_primality 78781488676897957459 (2 : ZMod 78781488676897957459)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (291817, 1), (2368147469641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (291817, 1), (2368147469641, 1)] : List FactorBlock).map factorBlockValue).prod) = 78781488676897957459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_291817
      · exact prime_oneHundredSixteenDJ_2368147469641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78781488676897957459) ^ 39390744338448978729 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 78781488676897957459) ^ 26260496225632652486 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 78781488676897957459) ^ 4146394140889366182 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 78781488676897957459) ^ 269968811539074 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 78781488676897957459) ^ 33267138 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_105644708210593840661 : Nat.Prime 105644708210593840661 := by
  apply lucas_primality 105644708210593840661 (2 : ZMod 105644708210593840661)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (229662409153464871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (229662409153464871, 1)] : List FactorBlock).map factorBlockValue).prod) = 105644708210593840661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_229662409153464871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105644708210593840661) ^ 52822354105296920330 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 105644708210593840661) ^ 21128941642118768132 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 105644708210593840661) ^ 4593248183069297420 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 105644708210593840661) ^ 460 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_139208738840258035657 : Nat.Prime 139208738840258035657 := by
  apply lucas_primality 139208738840258035657 (10 : ZMod 139208738840258035657)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (282563, 1), (1476581, 1), (13902173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (282563, 1), (1476581, 1), (13902173, 1)] : List FactorBlock).map factorBlockValue).prod) = 139208738840258035657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_282563
      · exact prime_oneHundredSixteenDJ_1476581
      · exact prime_oneHundredSixteenDJ_13902173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 139208738840258035657) ^ 69604369420129017828 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 139208738840258035657) ^ 46402912946752678552 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 139208738840258035657) ^ 492664428252312 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 139208738840258035657) ^ 94277753025576 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 139208738840258035657) ^ 10013451770472 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_147014748240104681581 : Nat.Prime 147014748240104681581 := by
  apply lucas_primality 147014748240104681581 (2 : ZMod 147014748240104681581)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 2), (14856007, 1), (28016477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 2), (14856007, 1), (28016477, 1)] : List FactorBlock).map factorBlockValue).prod) = 147014748240104681581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_14856007
      · exact prime_oneHundredSixteenDJ_28016477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147014748240104681581) ^ 73507374120052340790 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147014748240104681581) ^ 49004916080034893860 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147014748240104681581) ^ 29402949648020936316 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147014748240104681581) ^ 21002106891443525940 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147014748240104681581) ^ 5069474077244989020 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147014748240104681581) ^ 9895980005940 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147014748240104681581) ^ 5247438792540 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_220917667159773668549 : Nat.Prime 220917667159773668549 := by
  apply lucas_primality 220917667159773668549 (2 : ZMod 220917667159773668549)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55229416789943417137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55229416789943417137, 1)] : List FactorBlock).map factorBlockValue).prod) = 220917667159773668549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_55229416789943417137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 220917667159773668549) ^ 110458833579886834274 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 220917667159773668549) ^ 4 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_262107130272321792863 : Nat.Prime 262107130272321792863 := by
  apply lucas_primality 262107130272321792863 (5 : ZMod 262107130272321792863)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (421, 1), (1987, 1), (43411, 1), (212285419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (421, 1), (1987, 1), (43411, 1), (212285419, 1)] : List FactorBlock).map factorBlockValue).prod) = 262107130272321792863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_421
      · exact prime_oneHundredSixteenDJ_1987
      · exact prime_oneHundredSixteenDJ_43411
      · exact prime_oneHundredSixteenDJ_212285419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 262107130272321792863) ^ 131053565136160896431 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 262107130272321792863) ^ 15418066486607164286 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 262107130272321792863) ^ 622582257178911622 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 262107130272321792863) ^ 131910986548727626 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 262107130272321792863) ^ 6037804479793642 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 262107130272321792863) ^ 1234692102298 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_714402381236734082147 : Nat.Prime 714402381236734082147 := by
  apply lucas_primality 714402381236734082147 (2 : ZMod 714402381236734082147)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1123, 1), (1420277, 1), (13173803039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1123, 1), (1420277, 1), (13173803039, 1)] : List FactorBlock).map factorBlockValue).prod) = 714402381236734082147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_1123
      · exact prime_oneHundredSixteenDJ_1420277
      · exact prime_oneHundredSixteenDJ_13173803039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 714402381236734082147) ^ 357201190618367041073 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 714402381236734082147) ^ 42023669484513769538 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 714402381236734082147) ^ 636155281599941302 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 714402381236734082147) ^ 503002147635098 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 714402381236734082147) ^ 54229016414 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_893131836413501934313 : Nat.Prime 893131836413501934313 := by
  apply lucas_primality 893131836413501934313 (5 : ZMod 893131836413501934313)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (15937, 1), (34039, 1), (9799928863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (15937, 1), (34039, 1), (9799928863, 1)] : List FactorBlock).map factorBlockValue).prod) = 893131836413501934313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_15937
      · exact prime_oneHundredSixteenDJ_34039
      · exact prime_oneHundredSixteenDJ_9799928863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 893131836413501934313) ^ 446565918206750967156 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 893131836413501934313) ^ 297710612137833978104 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 893131836413501934313) ^ 127590262344785990616 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 893131836413501934313) ^ 56041402799366376 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 893131836413501934313) ^ 26238486336658008 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 893131836413501934313) ^ 91136563224 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_3440518411667972740747 : Nat.Prime 3440518411667972740747 := by
  apply lucas_primality 3440518411667972740747 (3 : ZMod 3440518411667972740747)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1993, 1), (424416887, 1), (677911001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1993, 1), (424416887, 1), (677911001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3440518411667972740747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_1993
      · exact prime_oneHundredSixteenDJ_424416887
      · exact prime_oneHundredSixteenDJ_677911001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3440518411667972740747) ^ 1720259205833986370373 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 1146839470555990913582 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 1726301260244843322 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 8106459749958 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 5075177134746 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_6964297121153883148751 : Nat.Prime 6964297121153883148751 := by
  apply lucas_primality 6964297121153883148751 (7 : ZMod 6964297121153883148751)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (7, 1), (419, 1), (316033, 1), (6010668571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (7, 1), (419, 1), (316033, 1), (6010668571, 1)] : List FactorBlock).map factorBlockValue).prod) = 6964297121153883148751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_419
      · exact prime_oneHundredSixteenDJ_316033
      · exact prime_oneHundredSixteenDJ_6010668571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6964297121153883148751) ^ 3482148560576941574375 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6964297121153883148751) ^ 1392859424230776629750 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6964297121153883148751) ^ 994899588736269021250 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6964297121153883148751) ^ 16621234179364876250 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6964297121153883148751) ^ 22036613648428750 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6964297121153883148751) ^ 1158655986250 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_10503910164012437880241 : Nat.Prime 10503910164012437880241 := by
  apply lucas_primality 10503910164012437880241 (29 : ZMod 10503910164012437880241)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (71, 1), (163, 1), (290904508172549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (71, 1), (163, 1), (290904508172549, 1)] : List FactorBlock).map factorBlockValue).prod) = 10503910164012437880241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_71
      · exact prime_oneHundredSixteenDJ_163
      · exact prime_oneHundredSixteenDJ_290904508172549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 10503910164012437880241) ^ 5251955082006218940120 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 3501303388004145960080 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 2100782032802487576048 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 807993089539418298480 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 147942396676231519440 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 64441166650383054480 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 36107760 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_21955136630064473066687 : Nat.Prime 21955136630064473066687 := by
  apply lucas_primality 21955136630064473066687 (7 : ZMod 21955136630064473066687)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (29, 1), (594249353923685191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (29, 1), (594249353923685191, 1)] : List FactorBlock).map factorBlockValue).prod) = 21955136630064473066687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_594249353923685191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21955136630064473066687) ^ 10977568315032236533343 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21955136630064473066687) ^ 3136448090009210438098 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21955136630064473066687) ^ 1688856663851113312822 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21955136630064473066687) ^ 757073676898774933334 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 21955136630064473066687) ^ 36946 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_29171898533146615426849 : Nat.Prime 29171898533146615426849 := by
  apply lucas_primality 29171898533146615426849 (29 : ZMod 29171898533146615426849)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (17874937826682975139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (17874937826682975139, 1)] : List FactorBlock).map factorBlockValue).prod) = 29171898533146615426849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_17874937826682975139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 29171898533146615426849) ^ 14585949266573307713424 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 29171898533146615426849) ^ 9723966177715538475616 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 29171898533146615426849) ^ 1715994031361565613344 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (29 : ZMod 29171898533146615426849) ^ 1632 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_40499879086497713578453 : Nat.Prime 40499879086497713578453 := by
  apply lucas_primality 40499879086497713578453 (5 : ZMod 40499879086497713578453)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (984593, 1), (17053741643647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (984593, 1), (17053741643647, 1)] : List FactorBlock).map factorBlockValue).prod) = 40499879086497713578453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_67
      · exact prime_oneHundredSixteenDJ_984593
      · exact prime_oneHundredSixteenDJ_17053741643647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40499879086497713578453) ^ 20249939543248856789226 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40499879086497713578453) ^ 13499959695499237859484 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40499879086497713578453) ^ 604475807261159904156 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40499879086497713578453) ^ 41133624844476564 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40499879086497713578453) ^ 2374838316 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_73919081295182374496213 : Nat.Prime 73919081295182374496213 := by
  apply lucas_primality 73919081295182374496213 (2 : ZMod 73919081295182374496213)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (127, 1), (3369419309, 1), (3925953061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (127, 1), (3369419309, 1), (3925953061, 1)] : List FactorBlock).map factorBlockValue).prod) = 73919081295182374496213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_127
      · exact prime_oneHundredSixteenDJ_3369419309
      · exact prime_oneHundredSixteenDJ_3925953061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73919081295182374496213) ^ 36959540647591187248106 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73919081295182374496213) ^ 6719916481380215863292 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73919081295182374496213) ^ 582040010198286413356 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73919081295182374496213) ^ 21938225704868 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73919081295182374496213) ^ 18828315098692 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_94671974659831205037179 : Nat.Prime 94671974659831205037179 := by
  apply lucas_primality 94671974659831205037179 (2 : ZMod 94671974659831205037179)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (893131836413501934313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (893131836413501934313, 1)] : List FactorBlock).map factorBlockValue).prod) = 94671974659831205037179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_53
      · exact prime_oneHundredSixteenDJ_893131836413501934313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94671974659831205037179) ^ 47335987329915602518589 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94671974659831205037179) ^ 1786263672827003868626 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94671974659831205037179) ^ 106 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_103907358637010497789397 : Nat.Prime 103907358637010497789397 := by
  apply lucas_primality 103907358637010497789397 (2 : ZMod 103907358637010497789397)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (107, 1), (127, 1), (24359, 1), (326159, 1), (21873451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (107, 1), (127, 1), (24359, 1), (326159, 1), (21873451, 1)] : List FactorBlock).map factorBlockValue).prod) = 103907358637010497789397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_107
      · exact prime_oneHundredSixteenDJ_127
      · exact prime_oneHundredSixteenDJ_24359
      · exact prime_oneHundredSixteenDJ_326159
      · exact prime_oneHundredSixteenDJ_21873451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103907358637010497789397) ^ 51953679318505248894698 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103907358637010497789397) ^ 9446123512455499799036 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103907358637010497789397) ^ 971096809691686895228 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103907358637010497789397) ^ 818168178244177147948 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103907358637010497789397) ^ 4265666022291986444 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103907358637010497789397) ^ 318578848466577644 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 103907358637010497789397) ^ 4750387062243196 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_161845234915907437936061 : Nat.Prime 161845234915907437936061 := by
  apply lucas_primality 161845234915907437936061 (7 : ZMod 161845234915907437936061)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2718109, 1), (2977166017181567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2718109, 1), (2977166017181567, 1)] : List FactorBlock).map factorBlockValue).prod) = 161845234915907437936061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_2718109
      · exact prime_oneHundredSixteenDJ_2977166017181567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 161845234915907437936061) ^ 80922617457953718968030 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 161845234915907437936061) ^ 32369046983181487587212 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 161845234915907437936061) ^ 59543320343631340 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 161845234915907437936061) ^ 54362180 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_185938401343770373050113 : Nat.Prime 185938401343770373050113 := by
  apply lucas_primality 185938401343770373050113 (3 : ZMod 185938401343770373050113)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (71, 1), (367651, 1), (27824990649587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (71, 1), (367651, 1), (27824990649587, 1)] : List FactorBlock).map factorBlockValue).prod) = 185938401343770373050113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_71
      · exact prime_oneHundredSixteenDJ_367651
      · exact prime_oneHundredSixteenDJ_27824990649587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 185938401343770373050113) ^ 92969200671885186525056 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185938401343770373050113) ^ 2618850723151695395072 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185938401343770373050113) ^ 505747030046893312 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185938401343770373050113) ^ 6682424576 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_232132903216728986520397 : Nat.Prime 232132903216728986520397 := by
  apply lucas_primality 232132903216728986520397 (6 : ZMod 232132903216728986520397)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (3203, 1), (49101347063840257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (3203, 1), (49101347063840257, 1)] : List FactorBlock).map factorBlockValue).prod) = 232132903216728986520397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_3203
      · exact prime_oneHundredSixteenDJ_49101347063840257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 232132903216728986520397) ^ 116066451608364493260198 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 232132903216728986520397) ^ 77377634405576328840132 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 232132903216728986520397) ^ 5661778127237292354156 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 232132903216728986520397) ^ 72473588266228219332 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 232132903216728986520397) ^ 4727628 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_235778156960716640089877 : Nat.Prime 235778156960716640089877 := by
  apply lucas_primality 235778156960716640089877 (2 : ZMod 235778156960716640089877)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (8543, 1), (985678153211136269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (8543, 1), (985678153211136269, 1)] : List FactorBlock).map factorBlockValue).prod) = 235778156960716640089877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_8543
      · exact prime_oneHundredSixteenDJ_985678153211136269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 235778156960716640089877) ^ 117889078480358320044938 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235778156960716640089877) ^ 33682593851530948584268 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235778156960716640089877) ^ 27598988289911815532 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235778156960716640089877) ^ 239204 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_368921715596727286790009 : Nat.Prime 368921715596727286790009 := by
  apply lucas_primality 368921715596727286790009 (3 : ZMod 368921715596727286790009)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (159715977601, 1), (288732631151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (159715977601, 1), (288732631151, 1)] : List FactorBlock).map factorBlockValue).prod) = 368921715596727286790009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_159715977601
      · exact prime_oneHundredSixteenDJ_288732631151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 368921715596727286790009) ^ 184460857798363643395004 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368921715596727286790009) ^ 2309861049208 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368921715596727286790009) ^ 1277727820808 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_449780291809503106123813 : Nat.Prime 449780291809503106123813 := by
  apply lucas_primality 449780291809503106123813 (2 : ZMod 449780291809503106123813)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (54105233779, 1), (98965052167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (54105233779, 1), (98965052167, 1)] : List FactorBlock).map factorBlockValue).prod) = 449780291809503106123813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_54105233779
      · exact prime_oneHundredSixteenDJ_98965052167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 449780291809503106123813) ^ 224890145904751553061906 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 449780291809503106123813) ^ 149926763936501035374604 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 449780291809503106123813) ^ 64254327401357586589116 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 449780291809503106123813) ^ 8313064382028 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 449780291809503106123813) ^ 4544839637436 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_567386366124394528945091 : Nat.Prime 567386366124394528945091 := by
  apply lucas_primality 567386366124394528945091 (6 : ZMod 567386366124394528945091)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (107, 1), (77854541, 1), (47629402349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (107, 1), (77854541, 1), (47629402349, 1)] : List FactorBlock).map factorBlockValue).prod) = 567386366124394528945091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_107
      · exact prime_oneHundredSixteenDJ_77854541
      · exact prime_oneHundredSixteenDJ_47629402349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 567386366124394528945091) ^ 283693183062197264472545 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 567386366124394528945091) ^ 113477273224878905789018 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 567386366124394528945091) ^ 51580578738581320813190 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 567386366124394528945091) ^ 43645105086491886841930 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 567386366124394528945091) ^ 5302676318919575036870 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 567386366124394528945091) ^ 7287774853420490 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (6 : ZMod 567386366124394528945091) ^ 11912523318410 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_831855096054489770910071 : Nat.Prime 831855096054489770910071 := by
  apply lucas_primality 831855096054489770910071 (31 : ZMod 831855096054489770910071)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (150889, 1), (5334911, 1), (103338683033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (150889, 1), (5334911, 1), (103338683033, 1)] : List FactorBlock).map factorBlockValue).prod) = 831855096054489770910071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_150889
      · exact prime_oneHundredSixteenDJ_5334911
      · exact prime_oneHundredSixteenDJ_103338683033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 831855096054489770910071) ^ 415927548027244885455035 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (31 : ZMod 831855096054489770910071) ^ 166371019210897954182014 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (31 : ZMod 831855096054489770910071) ^ 5513026768382650630 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (31 : ZMod 831855096054489770910071) ^ 155926705441663370 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (31 : ZMod 831855096054489770910071) ^ 8049793858790 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_967949511278107631005039 : Nat.Prime 967949511278107631005039 := by
  apply lucas_primality 967949511278107631005039 (3 : ZMod 967949511278107631005039)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (157, 1), (241, 1), (1669035451, 1), (2554578179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (157, 1), (241, 1), (1669035451, 1), (2554578179, 1)] : List FactorBlock).map factorBlockValue).prod) = 967949511278107631005039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_157
      · exact prime_oneHundredSixteenDJ_241
      · exact prime_oneHundredSixteenDJ_1669035451
      · exact prime_oneHundredSixteenDJ_2554578179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 967949511278107631005039) ^ 483974755639053815502519 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 322649837092702543668346 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 6165283511325526312134 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 4016388013602106352718 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 579945447352938 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 378907766156922 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1183930510596160135287671 : Nat.Prime 1183930510596160135287671 := by
  apply lucas_primality 1183930510596160135287671 (11 : ZMod 1183930510596160135287671)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (6964297121153883148751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (6964297121153883148751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1183930510596160135287671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_6964297121153883148751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1183930510596160135287671) ^ 591965255298080067643835 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1183930510596160135287671) ^ 236786102119232027057534 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1183930510596160135287671) ^ 69642971211538831487510 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1183930510596160135287671) ^ 170 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2652206744588512668806551 : Nat.Prime 2652206744588512668806551 := by
  apply lucas_primality 2652206744588512668806551 (3 : ZMod 2652206744588512668806551)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (83, 1), (1217, 1), (1883621, 1), (13275652681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (83, 1), (1217, 1), (1883621, 1), (13275652681, 1)] : List FactorBlock).map factorBlockValue).prod) = 2652206744588512668806551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_83
      · exact prime_oneHundredSixteenDJ_1217
      · exact prime_oneHundredSixteenDJ_1883621
      · exact prime_oneHundredSixteenDJ_13275652681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2652206744588512668806551) ^ 1326103372294256334403275 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 884068914862837556268850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 530441348917702533761310 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 378886677798358952686650 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 31954298127572441792850 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 2179298886268293072150 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 1408036300608515550 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2652206744588512668806551) ^ 199779762872550 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2854528318956111097979309 : Nat.Prime 2854528318956111097979309 := by
  apply lucas_primality 2854528318956111097979309 (2 : ZMod 2854528318956111097979309)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (67, 1), (3526779199, 1), (10522995737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (67, 1), (3526779199, 1), (10522995737, 1)] : List FactorBlock).map factorBlockValue).prod) = 2854528318956111097979309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_67
      · exact prime_oneHundredSixteenDJ_3526779199
      · exact prime_oneHundredSixteenDJ_10522995737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2854528318956111097979309) ^ 1427264159478055548989654 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2854528318956111097979309) ^ 407789759850873013997044 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2854528318956111097979309) ^ 69622641925758807267788 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2854528318956111097979309) ^ 42604900282927031313124 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2854528318956111097979309) ^ 809386740107092 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2854528318956111097979309) ^ 271265748870284 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_5709056637912222195958619 : Nat.Prime 5709056637912222195958619 := by
  apply lucas_primality 5709056637912222195958619 (2 : ZMod 5709056637912222195958619)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2854528318956111097979309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2854528318956111097979309, 1)] : List FactorBlock).map factorBlockValue).prod) = 5709056637912222195958619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_2854528318956111097979309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5709056637912222195958619) ^ 2854528318956111097979309 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5709056637912222195958619) ^ 2 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_7642830949394081675842507 : Nat.Prime 7642830949394081675842507 := by
  apply lucas_primality 7642830949394081675842507 (3 : ZMod 7642830949394081675842507)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (105243810493, 1), (12103373607107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (105243810493, 1), (12103373607107, 1)] : List FactorBlock).map factorBlockValue).prod) = 7642830949394081675842507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_105243810493
      · exact prime_oneHundredSixteenDJ_12103373607107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7642830949394081675842507) ^ 3821415474697040837921253 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7642830949394081675842507) ^ 2547610316464693891947502 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7642830949394081675842507) ^ 72620241642642 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7642830949394081675842507) ^ 631462862958 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_8248208248988236097390867 : Nat.Prime 8248208248988236097390867 := by
  apply lucas_primality 8248208248988236097390867 (2 : ZMod 8248208248988236097390867)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (239423, 1), (438521, 1), (3570924536941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (239423, 1), (438521, 1), (3570924536941, 1)] : List FactorBlock).map factorBlockValue).prod) = 8248208248988236097390867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_11
      · exact prime_oneHundredSixteenDJ_239423
      · exact prime_oneHundredSixteenDJ_438521
      · exact prime_oneHundredSixteenDJ_3570924536941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8248208248988236097390867) ^ 4124104124494118048695433 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8248208248988236097390867) ^ 749837113544385099762806 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8248208248988236097390867) ^ 34450358775005893742 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8248208248988236097390867) ^ 18809152238976550946 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8248208248988236097390867) ^ 2309824294426 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_10827645551549613263170531 : Nat.Prime 10827645551549613263170531 := by
  apply lucas_primality 10827645551549613263170531 (2 : ZMod 10827645551549613263170531)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (17, 1), (262107130272321792863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (17, 1), (262107130272321792863, 1)] : List FactorBlock).map factorBlockValue).prod) = 10827645551549613263170531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_262107130272321792863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10827645551549613263170531) ^ 5413822775774806631585265 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10827645551549613263170531) ^ 3609215183849871087723510 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10827645551549613263170531) ^ 2165529110309922652634106 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10827645551549613263170531) ^ 636920326561741956657090 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10827645551549613263170531) ^ 41310 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_11235700356867720923424377 : Nat.Prime 11235700356867720923424377 := by
  apply lucas_primality 11235700356867720923424377 (3 : ZMod 11235700356867720923424377)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (73919081295182374496213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (73919081295182374496213, 1)] : List FactorBlock).map factorBlockValue).prod) = 11235700356867720923424377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_73919081295182374496213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11235700356867720923424377) ^ 5617850178433860461712188 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11235700356867720923424377) ^ 591352650361458995969704 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11235700356867720923424377) ^ 152 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_12082015554217901646667073 : Nat.Prime 12082015554217901646667073 := by
  apply lucas_primality 12082015554217901646667073 (3 : ZMod 12082015554217901646667073)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (17, 1), (72251, 1), (153697439591436319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (17, 1), (72251, 1), (153697439591436319, 1)] : List FactorBlock).map factorBlockValue).prod) = 12082015554217901646667073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_72251
      · exact prime_oneHundredSixteenDJ_153697439591436319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12082015554217901646667073) ^ 6041007777108950823333536 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12082015554217901646667073) ^ 710706797306935390980416 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12082015554217901646667073) ^ 167222814275482715072 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12082015554217901646667073) ^ 78609088 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_16743127646920693638300323 : Nat.Prime 16743127646920693638300323 := by
  apply lucas_primality 16743127646920693638300323 (2 : ZMod 16743127646920693638300323)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3229, 1), (51850223, 1), (2941297796699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3229, 1), (51850223, 1), (2941297796699, 1)] : List FactorBlock).map factorBlockValue).prod) = 16743127646920693638300323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_3229
      · exact prime_oneHundredSixteenDJ_51850223
      · exact prime_oneHundredSixteenDJ_2941297796699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16743127646920693638300323) ^ 8371563823460346819150161 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16743127646920693638300323) ^ 984889861583570214017666 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16743127646920693638300323) ^ 5185236186720561671818 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16743127646920693638300323) ^ 322913319908396414 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16743127646920693638300323) ^ 5692428582278 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_30584959535220205528839863 : Nat.Prime 30584959535220205528839863 := by
  apply lucas_primality 30584959535220205528839863 (5 : ZMod 30584959535220205528839863)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (52600043, 1), (17101842167483201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (52600043, 1), (17101842167483201, 1)] : List FactorBlock).map factorBlockValue).prod) = 30584959535220205528839863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_52600043
      · exact prime_oneHundredSixteenDJ_17101842167483201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30584959535220205528839863) ^ 15292479767610102764419931 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 30584959535220205528839863) ^ 1799115266777659148755286 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 30584959535220205528839863) ^ 581462633694428834 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 30584959535220205528839863) ^ 1788401462 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_32927481045840912747015113 : Nat.Prime 32927481045840912747015113 := by
  apply lucas_primality 32927481045840912747015113 (3 : ZMod 32927481045840912747015113)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (337, 1), (286063, 1), (1856303979439153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (337, 1), (286063, 1), (1856303979439153, 1)] : List FactorBlock).map factorBlockValue).prod) = 32927481045840912747015113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_23
      · exact prime_oneHundredSixteenDJ_337
      · exact prime_oneHundredSixteenDJ_286063
      · exact prime_oneHundredSixteenDJ_1856303979439153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32927481045840912747015113) ^ 16463740522920456373507556 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 32927481045840912747015113) ^ 1431629610688735336826744 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 32927481045840912747015113) ^ 97707658889735646133576 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 32927481045840912747015113) ^ 115105697157062999224 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 32927481045840912747015113) ^ 17738194504 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_34432075961819583628249547 : Nat.Prime 34432075961819583628249547 := by
  apply lucas_primality 34432075961819583628249547 (2 : ZMod 34432075961819583628249547)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (36901, 1), (27443920666759854769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (36901, 1), (27443920666759854769, 1)] : List FactorBlock).map factorBlockValue).prod) = 34432075961819583628249547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_36901
      · exact prime_oneHundredSixteenDJ_27443920666759854769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34432075961819583628249547) ^ 17216037980909791814124773 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34432075961819583628249547) ^ 2025416233048210801661738 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34432075961819583628249547) ^ 933093302669835062146 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34432075961819583628249547) ^ 1254634 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_36935889726885914783549137 : Nat.Prime 36935889726885914783549137 := by
  apply lucas_primality 36935889726885914783549137 (7 : ZMod 36935889726885914783549137)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (40499879086497713578453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (40499879086497713578453, 1)] : List FactorBlock).map factorBlockValue).prod) = 36935889726885914783549137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_19
      · exact prime_oneHundredSixteenDJ_40499879086497713578453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36935889726885914783549137) ^ 18467944863442957391774568 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 36935889726885914783549137) ^ 12311963242295304927849712 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 36935889726885914783549137) ^ 1943994196151890251765744 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 36935889726885914783549137) ^ 912 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_72370954383075145958479127 : Nat.Prime 72370954383075145958479127 := by
  apply lucas_primality 72370954383075145958479127 (5 : ZMod 72370954383075145958479127)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8821, 1), (15919, 1), (316703, 1), (387449, 1), (2100071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8821, 1), (15919, 1), (316703, 1), (387449, 1), (2100071, 1)] : List FactorBlock).map factorBlockValue).prod) = 72370954383075145958479127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_8821
      · exact prime_oneHundredSixteenDJ_15919
      · exact prime_oneHundredSixteenDJ_316703
      · exact prime_oneHundredSixteenDJ_387449
      · exact prime_oneHundredSixteenDJ_2100071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 72370954383075145958479127) ^ 36185477191537572979239563 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72370954383075145958479127) ^ 8204393422863070622206 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72370954383075145958479127) ^ 4546199785355559140554 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72370954383075145958479127) ^ 228513637013464179242 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72370954383075145958479127) ^ 186788337001967087174 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72370954383075145958479127) ^ 34461194113472899706 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_103582294981818279147521107 : Nat.Prime 103582294981818279147521107 := by
  apply lucas_primality 103582294981818279147521107 (3 : ZMod 103582294981818279147521107)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6951563, 1), (2483429385636445577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6951563, 1), (2483429385636445577, 1)] : List FactorBlock).map factorBlockValue).prod) = 103582294981818279147521107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_6951563
      · exact prime_oneHundredSixteenDJ_2483429385636445577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 103582294981818279147521107) ^ 51791147490909139573760553 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 103582294981818279147521107) ^ 34527431660606093049173702 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 103582294981818279147521107) ^ 14900576313818673462 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 103582294981818279147521107) ^ 41709378 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_324983314113572041685587549 : Nat.Prime 324983314113572041685587549 := by
  apply lucas_primality 324983314113572041685587549 (2 : ZMod 324983314113572041685587549)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (73, 1), (269, 1), (410561, 1), (1119710445925699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (73, 1), (269, 1), (410561, 1), (1119710445925699, 1)] : List FactorBlock).map factorBlockValue).prod) = 324983314113572041685587549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_73
      · exact prime_oneHundredSixteenDJ_269
      · exact prime_oneHundredSixteenDJ_410561
      · exact prime_oneHundredSixteenDJ_1119710445925699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 324983314113572041685587549) ^ 162491657056786020842793774 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 324983314113572041685587549) ^ 108327771371190680561862516 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 324983314113572041685587549) ^ 4451826220733863584734076 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 324983314113572041685587549) ^ 1208116409344133983961292 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 324983314113572041685587549) ^ 791559144959146245468 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 324983314113572041685587549) ^ 290238708852 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_425909809179898762705956353 : Nat.Prime 425909809179898762705956353 := by
  apply lucas_primality 425909809179898762705956353 (3 : ZMod 425909809179898762705956353)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (831855096054489770910071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (831855096054489770910071, 1)] : List FactorBlock).map factorBlockValue).prod) = 425909809179898762705956353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_831855096054489770910071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 425909809179898762705956353) ^ 212954904589949381352978176 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 425909809179898762705956353) ^ 512 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_427236631015350160720616653 : Nat.Prime 427236631015350160720616653 := by
  apply lucas_primality 427236631015350160720616653 (2 : ZMod 427236631015350160720616653)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (157, 1), (181, 1), (139208738840258035657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (157, 1), (181, 1), (139208738840258035657, 1)] : List FactorBlock).map factorBlockValue).prod) = 427236631015350160720616653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_157
      · exact prime_oneHundredSixteenDJ_181
      · exact prime_oneHundredSixteenDJ_139208738840258035657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 427236631015350160720616653) ^ 213618315507675080360308326 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 427236631015350160720616653) ^ 142412210338450053573538884 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 427236631015350160720616653) ^ 2721252426849364081023036 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 427236631015350160720616653) ^ 2360423375775415252600092 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 427236631015350160720616653) ^ 3069036 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_436761014509322935004197279 : Nat.Prime 436761014509322935004197279 := by
  apply lucas_primality 436761014509322935004197279 (3 : ZMod 436761014509322935004197279)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (107, 1), (181, 1), (139208738840258035657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (107, 1), (181, 1), (139208738840258035657, 1)] : List FactorBlock).map factorBlockValue).prod) = 436761014509322935004197279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_107
      · exact prime_oneHundredSixteenDJ_181
      · exact prime_oneHundredSixteenDJ_139208738840258035657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 436761014509322935004197279) ^ 218380507254661467502098639 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 436761014509322935004197279) ^ 145587004836440978334732426 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 436761014509322935004197279) ^ 4081878640274046121534554 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 436761014509322935004197279) ^ 2413044279057032790078438 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 436761014509322935004197279) ^ 3137454 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_507936883540471857745622021 : Nat.Prime 507936883540471857745622021 := by
  apply lucas_primality 507936883540471857745622021 (10 : ZMod 507936883540471857745622021)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (7405967, 1), (9952799, 1), (7031640653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (7405967, 1), (9952799, 1), (7031640653, 1)] : List FactorBlock).map factorBlockValue).prod) = 507936883540471857745622021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_7
      · exact prime_oneHundredSixteenDJ_7405967
      · exact prime_oneHundredSixteenDJ_9952799
      · exact prime_oneHundredSixteenDJ_7031640653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 507936883540471857745622021) ^ 253968441770235928872811010 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 507936883540471857745622021) ^ 101587376708094371549124404 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 507936883540471857745622021) ^ 72562411934353122535088860 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 507936883540471857745622021) ^ 68584815938346992060 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 507936883540471857745622021) ^ 51034576659336921980 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (10 : ZMod 507936883540471857745622021) ^ 72235898932600340 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_672269404685918635251558557 : Nat.Prime 672269404685918635251558557 := by
  apply lucas_primality 672269404685918635251558557 (2 : ZMod 672269404685918635251558557)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (1629923, 1), (356794724615209037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (1629923, 1), (356794724615209037, 1)] : List FactorBlock).map factorBlockValue).prod) = 672269404685918635251558557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_1629923
      · exact prime_oneHundredSixteenDJ_356794724615209037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 672269404685918635251558557) ^ 336134702342959317625779278 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 672269404685918635251558557) ^ 39545259099171684426562268 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 672269404685918635251558557) ^ 412454701655181646772 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 672269404685918635251558557) ^ 1884190988 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1133412880627499186705106989 : Nat.Prime 1133412880627499186705106989 := by
  apply lucas_primality 1133412880627499186705106989 (2 : ZMod 1133412880627499186705106989)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (73, 1), (94671974659831205037179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (73, 1), (94671974659831205037179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1133412880627499186705106989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_41
      · exact prime_oneHundredSixteenDJ_73
      · exact prime_oneHundredSixteenDJ_94671974659831205037179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1133412880627499186705106989) ^ 566706440313749593352553494 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133412880627499186705106989) ^ 27644216600670711870856268 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133412880627499186705106989) ^ 15526203844212317626097356 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133412880627499186705106989) ^ 11972 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1172162038939550440951435433 : Nat.Prime 1172162038939550440951435433 := by
  apply lucas_primality 1172162038939550440951435433 (3 : ZMod 1172162038939550440951435433)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1859831, 1), (78781488676897957459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1859831, 1), (78781488676897957459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1172162038939550440951435433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_1859831
      · exact prime_oneHundredSixteenDJ_78781488676897957459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1172162038939550440951435433) ^ 586081019469775220475717716 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1172162038939550440951435433) ^ 630251909415183659672 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1172162038939550440951435433) ^ 14878648 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_1781077383843213007679453839 : Nat.Prime 1781077383843213007679453839 := by
  apply lucas_primality 1781077383843213007679453839 (3 : ZMod 1781077383843213007679453839)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (3541, 1), (294409061, 1), (5583213862823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (3541, 1), (294409061, 1), (5583213862823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1781077383843213007679453839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_17
      · exact prime_oneHundredSixteenDJ_3541
      · exact prime_oneHundredSixteenDJ_294409061
      · exact prime_oneHundredSixteenDJ_5583213862823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1781077383843213007679453839) ^ 890538691921606503839726919 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1781077383843213007679453839) ^ 593692461281071002559817946 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1781077383843213007679453839) ^ 104769257873130176922320814 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1781077383843213007679453839) ^ 502987117719066085196118 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1781077383843213007679453839) ^ 6049669048206410358 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1781077383843213007679453839) ^ 319005760410306 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_2742859171118548031826358913 : Nat.Prime 2742859171118548031826358913 := by
  apply lucas_primality 2742859171118548031826358913 (3 : ZMod 2742859171118548031826358913)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2742859171118548031826358913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_171401
      · exact prime_oneHundredSixteenDJ_714027719
      · exact prime_oneHundredSixteenDJ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2742859171118548031826358913) ^ 1371429585559274015913179456 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2742859171118548031826358913) ^ 94581350728225794200908928 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2742859171118548031826358913) ^ 16002585580705760362112 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2742859171118548031826358913) ^ 3841390324397963648 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2742859171118548031826358913) ^ 454293361518752128 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_4285717454872731299728685801 : Nat.Prime 4285717454872731299728685801 := by
  apply lucas_primality 4285717454872731299728685801 (3 : ZMod 4285717454872731299728685801)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 4285717454872731299728685801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_29
      · exact prime_oneHundredSixteenDJ_171401
      · exact prime_oneHundredSixteenDJ_714027719
      · exact prime_oneHundredSixteenDJ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4285717454872731299728685801) ^ 2142858727436365649864342900 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 857143490974546259945737160 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 25004039969852750565800 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 6002172381871818200 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 709833377373050200 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_17142869819490925198914743207 : Nat.Prime 17142869819490925198914743207 := by
  apply lucas_primality 17142869819490925198914743207 (5 : ZMod 17142869819490925198914743207)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (8231, 1), (150343, 1), (235871, 1), (2258914624817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (8231, 1), (150343, 1), (235871, 1), (2258914624817, 1)] : List FactorBlock).map factorBlockValue).prod) = 17142869819490925198914743207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_13
      · exact prime_oneHundredSixteenDJ_8231
      · exact prime_oneHundredSixteenDJ_150343
      · exact prime_oneHundredSixteenDJ_235871
      · exact prime_oneHundredSixteenDJ_2258914624817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17142869819490925198914743207) ^ 8571434909745462599457371603 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 1318682293806994246070364862 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 2082720182176032705493226 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 114025061489333891161642 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 72679005979925150607386 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 7588985272464518 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_45714319518642467197105981867 : Nat.Prime 45714319518642467197105981867 := by
  apply lucas_primality 45714319518642467197105981867 (3 : ZMod 45714319518642467197105981867)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (821, 1), (266117, 1), (564257, 1), (61802817949039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (821, 1), (266117, 1), (564257, 1), (61802817949039, 1)] : List FactorBlock).map factorBlockValue).prod) = 45714319518642467197105981867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_821
      · exact prime_oneHundredSixteenDJ_266117
      · exact prime_oneHundredSixteenDJ_564257
      · exact prime_oneHundredSixteenDJ_61802817949039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45714319518642467197105981867) ^ 22857159759321233598552990933 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981867) ^ 15238106506214155732368660622 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981867) ^ 55681266161562079411822146 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981867) ^ 171782785461441648587298 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981867) ^ 81016840763415371359338 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981867) ^ 739680180219894 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_45714319518642467197105981889 : Nat.Prime 45714319518642467197105981889 := by
  apply lucas_primality 45714319518642467197105981889 (3 : ZMod 45714319518642467197105981889)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (899893, 1), (403945337, 1), (1964983069187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (899893, 1), (403945337, 1), (1964983069187, 1)] : List FactorBlock).map factorBlockValue).prod) = 45714319518642467197105981889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_899893
      · exact prime_oneHundredSixteenDJ_403945337
      · exact prime_oneHundredSixteenDJ_1964983069187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45714319518642467197105981889) ^ 22857159759321233598552990944 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981889) ^ 50799727877250369985216 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981889) ^ 113169568581113407424 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45714319518642467197105981889) ^ 23264485193532224 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_68571479277963700795658972843 : Nat.Prime 68571479277963700795658972843 := by
  apply lucas_primality 68571479277963700795658972843 (2 : ZMod 68571479277963700795658972843)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (677, 1), (359326039, 1), (140940615619369207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (677, 1), (359326039, 1), (140940615619369207, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963700795658972843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_677
      · exact prime_oneHundredSixteenDJ_359326039
      · exact prime_oneHundredSixteenDJ_140940615619369207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68571479277963700795658972843) ^ 34285739638981850397829486421 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68571479277963700795658972843) ^ 101287266289458937659762146 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68571479277963700795658972843) ^ 190833593548625906278 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68571479277963700795658972843) ^ 486527456806 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixteenDJ_137142958555927401591317945641 : Nat.Prime 137142958555927401591317945641 := by
  apply lucas_primality 137142958555927401591317945641 (7 : ZMod 137142958555927401591317945641)
  · rw [← oneHundredSixteenDJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (8179, 1), (11649479, 1), (11994594132657967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (8179, 1), (11649479, 1), (11994594132657967, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixteenDJ_2
      · exact prime_oneHundredSixteenDJ_3
      · exact prime_oneHundredSixteenDJ_5
      · exact prime_oneHundredSixteenDJ_8179
      · exact prime_oneHundredSixteenDJ_11649479
      · exact prime_oneHundredSixteenDJ_11994594132657967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 137142958555927401591317945641) ^ 68571479277963700795658972820 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 137142958555927401591317945641) ^ 45714319518642467197105981880 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 137142958555927401591317945641) ^ 27428591711185480318263589128 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 137142958555927401591317945641) ^ 16767692695430664089903160 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 137142958555927401591317945641) ^ 11772454249321141451160 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide
    · change (7 : ZMod 137142958555927401591317945641) ^ 11433730648920 ≠ 1
      rw [← oneHundredSixteenDJFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945600 : Nat.totient 137142958555927401591317945600 = 52965247309410099091857408000 := by
  rw [← show ((([(2, 8), (5, 2), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_29, prime_oneHundredSixteenDJ_171401, prime_oneHundredSixteenDJ_714027719, prime_oneHundredSixteenDJ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945601 : Nat.totient 137142958555927401591317945601 = 91428639037284934394211963732 := by
  rw [← show ((([(3, 1), (45714319518642467197105981867, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_45714319518642467197105981867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945602 : Nat.totient 137142958555927401591317945602 = 65993415278886475959117127680 := by
  rw [← show ((([(2, 1), (61, 1), (79, 1), (113, 1), (6089, 1), (4841303, 1), (4271691791749, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_61, prime_oneHundredSixteenDJ_79, prime_oneHundredSixteenDJ_113, prime_oneHundredSixteenDJ_6089, prime_oneHundredSixteenDJ_4841303, prime_oneHundredSixteenDJ_4271691791749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945603 : Nat.totient 137142958555927401591317945603 = 106864643030592780460767230280 := by
  rw [← show ((([(7, 1), (11, 1), (1781077383843213007679453839, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_1781077383843213007679453839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945604 : Nat.totient 137142958555927401591317945604 = 45714305756568820525201731840 := by
  rw [← show ((([(2, 2), (3, 1), (3321761, 1), (3440518411667972740747, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_3321761, prime_oneHundredSixteenDJ_3440518411667972740747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945605 : Nat.totient 137142958555927401591317945605 = 109714366256682928311889348800 := by
  rw [← show ((([(5, 1), (186570341, 1), (147014748240104681581, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_186570341, prime_oneHundredSixteenDJ_147014748240104681581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945606 : Nat.totient 137142958555927401591317945606 = 68134718263454377860654775368 := by
  rw [← show ((([(2, 1), (157, 1), (436761014509322935004197279, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_157, prime_oneHundredSixteenDJ_436761014509322935004197279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945607 : Nat.totient 137142958555927401591317945607 = 91428616000877931455464999680 := by
  rw [← show ((([(3, 2), (4137359, 1), (97461977, 1), (37789624941161, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_4137359, prime_oneHundredSixteenDJ_97461977, prime_oneHundredSixteenDJ_37789624941161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945608 : Nat.totient 137142958555927401591317945608 = 68540907954166124468955593808 := by
  rw [← show ((([(2, 3), (2243, 1), (7642830949394081675842507, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_2243, prime_oneHundredSixteenDJ_7642830949394081675842507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945609 : Nat.totient 137142958555927401591317945609 = 126494521706483588789586320976 := by
  rw [← show ((([(13, 1), (1279, 1), (8248208248988236097390867, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_1279, prime_oneHundredSixteenDJ_8248208248988236097390867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945610 : Nat.totient 137142958555927401591317945610 = 31319727410066577997768968000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1151, 1), (567386366124394528945091, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_1151, prime_oneHundredSixteenDJ_567386366124394528945091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945611 : Nat.totient 137142958555927401591317945611 = 126065386503613795650557644800 := by
  rw [← show ((([(17, 1), (43, 1), (14891, 1), (1388473, 1), (6060581, 1), (1497202607, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_17, prime_oneHundredSixteenDJ_43, prime_oneHundredSixteenDJ_14891, prime_oneHundredSixteenDJ_1388473, prime_oneHundredSixteenDJ_6060581, prime_oneHundredSixteenDJ_1497202607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945612 : Nat.totient 137142958555927401591317945612 = 67590970953096642850734700800 := by
  rw [← show ((([(2, 2), (71, 1), (4597, 1), (10622309, 1), (9889213193728541, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_71, prime_oneHundredSixteenDJ_4597, prime_oneHundredSixteenDJ_10622309, prime_oneHundredSixteenDJ_9889213193728541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945613 : Nat.totient 137142958555927401591317945613 = 90574165775254234072770730224 := by
  rw [← show ((([(3, 1), (107, 1), (427236631015350160720616653, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_107, prime_oneHundredSixteenDJ_427236631015350160720616653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945614 : Nat.totient 137142958555927401591317945614 = 60651041352626602696517959680 := by
  rw [← show ((([(2, 1), (11, 1), (37, 1), (32537, 1), (2009402137, 1), (2576942583329, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_37, prime_oneHundredSixteenDJ_32537, prime_oneHundredSixteenDJ_2009402137, prime_oneHundredSixteenDJ_2576942583329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945615 : Nat.totient 137142958555927401591317945615 = 108920472315740708139154129536 := by
  rw [← show ((([(5, 1), (173, 1), (683, 1), (232132903216728986520397, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_173, prime_oneHundredSixteenDJ_683, prime_oneHundredSixteenDJ_232132903216728986520397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945616 : Nat.totient 137142958555927401591317945616 = 43305838222118674295312386560 := by
  rw [← show ((([(2, 4), (3, 5), (19, 1), (17573, 1), (105644708210593840661, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_19, prime_oneHundredSixteenDJ_17573, prime_oneHundredSixteenDJ_105644708210593840661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945617 : Nat.totient 137142958555927401591317945617 = 116472656802132176005913952960 := by
  rw [← show ((([(7, 1), (109, 1), (21088424999, 1), (8523242221328741, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_109, prime_oneHundredSixteenDJ_21088424999, prime_oneHundredSixteenDJ_8523242221328741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945618 : Nat.totient 137142958555927401591317945618 = 68565770221325788573463002180 := by
  rw [← show ((([(2, 1), (12011, 1), (5709056637912222195958619, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_12011, prime_oneHundredSixteenDJ_5709056637912222195958619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945619 : Nat.totient 137142958555927401591317945619 = 91428638755859622028363445280 := by
  rw [← show ((([(3, 1), (380305279, 1), (2329702477, 1), (51596405131, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_380305279, prime_oneHundredSixteenDJ_2329702477, prime_oneHundredSixteenDJ_51596405131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945620 : Nat.totient 137142958555927401591317945620 = 50421773217973294671682283520 := by
  rw [← show ((([(2, 2), (5, 1), (23, 1), (31, 1), (149, 1), (2999, 1), (1069223, 1), (20129035334069, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_23, prime_oneHundredSixteenDJ_31, prime_oneHundredSixteenDJ_149, prime_oneHundredSixteenDJ_2999, prime_oneHundredSixteenDJ_1069223, prime_oneHundredSixteenDJ_20129035334069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945621 : Nat.totient 137142958555927401591317945621 = 135264155939024926662780687360 := by
  rw [← show ((([(73, 1), (1168859, 1), (8335031, 1), (192832978518113, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_73, prime_oneHundredSixteenDJ_1168859, prime_oneHundredSixteenDJ_8335031, prime_oneHundredSixteenDJ_192832978518113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945622 : Nat.totient 137142958555927401591317945622 = 42195285369404789422955097600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (16561, 1), (5315870831, 1), (19971833404739, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_16561, prime_oneHundredSixteenDJ_5315870831, prime_oneHundredSixteenDJ_19971833404739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945623 : Nat.totient 137142958555927401591317945623 = 137130876540373183689671267200 := by
  rw [← show ((([(11351, 1), (12082015554217901646667073, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_11351, prime_oneHundredSixteenDJ_12082015554217901646667073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945624 : Nat.totient 137142958555927401591317945624 = 58378184929770644796305817600 := by
  rw [← show ((([(2, 3), (7, 1), (151, 1), (13597, 1), (15233, 1), (78303288274877279, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_151, prime_oneHundredSixteenDJ_13597, prime_oneHundredSixteenDJ_15233, prime_oneHundredSixteenDJ_78303288274877279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945625 : Nat.totient 137142958555927401591317945625 = 66350316025504581972480000000 := by
  rw [← show ((([(3, 2), (5, 4), (11, 1), (577, 2), (2371, 1), (21522701, 1), (130460293, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_577, prime_oneHundredSixteenDJ_2371, prime_oneHundredSixteenDJ_21522701, prime_oneHundredSixteenDJ_130460293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945626 : Nat.totient 137142958555927401591317945626 = 68056826130634587800107434496 := by
  rw [← show ((([(2, 1), (137, 1), (4817, 1), (103907358637010497789397, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_137, prime_oneHundredSixteenDJ_4817, prime_oneHundredSixteenDJ_103907358637010497789397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945627 : Nat.totient 137142958555927401591317945627 = 137141774625416805431182542120 := by
  rw [← show ((([(115837, 1), (1183930510596160135287671, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_115837, prime_oneHundredSixteenDJ_1183930510596160135287671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945628 : Nat.totient 137142958555927401591317945628 = 43025241899898792656099747584 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (672269404685918635251558557, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_17, prime_oneHundredSixteenDJ_672269404685918635251558557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945629 : Nat.totient 137142958555927401591317945629 = 132396378216271035905712885120 := by
  rw [← show ((([(29, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_29, prime_oneHundredSixteenDJ_7561, prime_oneHundredSixteenDJ_2416168199, prime_oneHundredSixteenDJ_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945630 : Nat.totient 137142958555927401591317945630 = 53519159091620073467421388800 := by
  rw [← show ((([(2, 1), (5, 1), (41, 1), (1454149, 1), (7190737, 1), (31989492017311, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_41, prime_oneHundredSixteenDJ_1454149, prime_oneHundredSixteenDJ_7190737, prime_oneHundredSixteenDJ_31989492017311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945631 : Nat.totient 137142958555927401591317945631 = 78365462746282381448640252000 := by
  rw [← show ((([(3, 1), (7, 1), (40351, 1), (161845234915907437936061, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_40351, prime_oneHundredSixteenDJ_161845234915907437936061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945632 : Nat.totient 137142958555927401591317945632 = 68571479277963700795658972800 := by
  rw [← show ((([(2, 5), (4285717454872731299728685801, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_4285717454872731299728685801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945633 : Nat.totient 137142958555927401591317945633 = 134818501631243436904349472048 := by
  rw [← show ((([(59, 1), (22831969868053, 1), (101807112487879, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_59, prime_oneHundredSixteenDJ_22831969868053, prime_oneHundredSixteenDJ_101807112487879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945634 : Nat.totient 137142958555927401591317945634 = 44741152099608774886422552960 := by
  rw [← show ((([(2, 1), (3, 2), (47, 1), (85661, 1), (3760206607, 1), (503278413277, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_47, prime_oneHundredSixteenDJ_85661, prime_oneHundredSixteenDJ_3760206607, prime_oneHundredSixteenDJ_503278413277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945635 : Nat.totient 137142958555927401591317945635 = 95944547520314654434686211968 := by
  rw [← show ((([(5, 1), (13, 1), (19, 1), (25037033243, 1), (4435307048044387, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_19, prime_oneHundredSixteenDJ_25037033243, prime_oneHundredSixteenDJ_4435307048044387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945636 : Nat.totient 137142958555927401591317945636 = 62333989666485579861319546880 := by
  rw [← show ((([(2, 2), (11, 1), (16763, 1), (185938401343770373050113, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_16763, prime_oneHundredSixteenDJ_185938401343770373050113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945637 : Nat.totient 137142958555927401591317945637 = 91428465570076129152573273600 := by
  rw [← show ((([(3, 1), (825991, 1), (2064437, 1), (4949221, 1), (5416745897, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_825991, prime_oneHundredSixteenDJ_2064437, prime_oneHundredSixteenDJ_4949221, prime_oneHundredSixteenDJ_5416745897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945638 : Nat.totient 137142958555927401591317945638 = 57665622494785115716290178560 := by
  rw [← show ((([(2, 1), (7, 1), (53, 1), (61471, 1), (2833553, 1), (1061128527711503, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_53, prime_oneHundredSixteenDJ_61471, prime_oneHundredSixteenDJ_2833553, prime_oneHundredSixteenDJ_1061128527711503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945639 : Nat.totient 137142958555927401591317945639 = 137141129532799133993968783360 := by
  rw [← show ((([(75041, 1), (94617863, 1), (19315313717444033, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_75041, prime_oneHundredSixteenDJ_94617863, prime_oneHundredSixteenDJ_19315313717444033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945640 : Nat.totient 137142958555927401591317945640 = 36566981091257883058579684608 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (8179, 1), (11649479, 1), (11994594132657967, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_8179, prime_oneHundredSixteenDJ_11649479, prime_oneHundredSixteenDJ_11994594132657967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945641 : Nat.totient 137142958555927401591317945641 = 137142958555927401591317945640 := by
  rw [← show ((([(137142958555927401591317945641, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_137142958555927401591317945641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945642 : Nat.totient 137142958555927401591317945642 = 68571041264510251504697210880 := by
  rw [← show ((([(2, 1), (158761, 1), (14729849, 1), (51933437, 1), (564617497, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_158761, prime_oneHundredSixteenDJ_14729849, prime_oneHundredSixteenDJ_51933437, prime_oneHundredSixteenDJ_564617497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945643 : Nat.totient 137142958555927401591317945643 = 87275367822715982712264480480 := by
  rw [← show ((([(3, 3), (23, 1), (491, 1), (449780291809503106123813, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_23, prime_oneHundredSixteenDJ_491, prime_oneHundredSixteenDJ_449780291809503106123813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945644 : Nat.totient 137142958555927401591317945644 = 66894650289402483693655572480 := by
  rw [← show ((([(2, 2), (67, 1), (179, 1), (257, 1), (4591, 1), (924527, 1), (2620750481123, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_67, prime_oneHundredSixteenDJ_179, prime_oneHundredSixteenDJ_257, prime_oneHundredSixteenDJ_4591, prime_oneHundredSixteenDJ_924527, prime_oneHundredSixteenDJ_2620750481123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945645 : Nat.totient 137142958555927401591317945645 = 88509069051220373463976621056 := by
  rw [← show ((([(5, 1), (7, 2), (17, 1), (32927481045840912747015113, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_17, prime_oneHundredSixteenDJ_32927481045840912747015113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945646 : Nat.totient 137142958555927401591317945646 = 45692664227539367970579636600 := by
  rw [← show ((([(2, 1), (3, 1), (2111, 1), (10827645551549613263170531, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_2111, prime_oneHundredSixteenDJ_10827645551549613263170531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945647 : Nat.totient 137142958555927401591317945647 = 124675416859678466322209054400 := by
  rw [← show ((([(11, 1), (13339342297, 1), (934644408195929141, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_13339342297, prime_oneHundredSixteenDJ_934644408195929141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945648 : Nat.totient 137142958555927401591317945648 = 63288370775631102474799411200 := by
  rw [← show ((([(2, 4), (13, 1), (8231, 1), (150343, 1), (235871, 1), (2258914624817, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_8231, prime_oneHundredSixteenDJ_150343, prime_oneHundredSixteenDJ_235871, prime_oneHundredSixteenDJ_2258914624817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945649 : Nat.totient 137142958555927401591317945649 = 91428580693487868100977975936 := by
  rw [← show ((([(3, 1), (1567067, 1), (29171898533146615426849, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_1567067, prime_oneHundredSixteenDJ_29171898533146615426849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945650 : Nat.totient 137142958555927401591317945650 = 54857183422370960636527178240 := by
  rw [← show ((([(2, 1), (5, 2), (2742859171118548031826358913, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_2742859171118548031826358913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945651 : Nat.totient 137142958555927401591317945651 = 129099703049006766068068876800 := by
  rw [← show ((([(31, 1), (37, 1), (4159, 1), (105653, 1), (6952349, 1), (39138824471, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_31, prime_oneHundredSixteenDJ_37, prime_oneHundredSixteenDJ_4159, prime_oneHundredSixteenDJ_105653, prime_oneHundredSixteenDJ_6952349, prime_oneHundredSixteenDJ_39138824471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945652 : Nat.totient 137142958555927401591317945652 = 38836569221450403121878082560 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (197, 1), (263, 1), (10503910164012437880241, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_197, prime_oneHundredSixteenDJ_263, prime_oneHundredSixteenDJ_10503910164012437880241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945653 : Nat.totient 137142958555927401591317945653 = 137142225736308654461339013120 := by
  rw [← show ((([(187177, 1), (1068723629, 1), (685576022919041, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_187177, prime_oneHundredSixteenDJ_1068723629, prime_oneHundredSixteenDJ_685576022919041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945654 : Nat.totient 137142958555927401591317945654 = 63071074956619997711992840320 := by
  rw [← show ((([(2, 1), (19, 1), (43, 1), (181, 1), (2099, 1), (220917667159773668549, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_19, prime_oneHundredSixteenDJ_43, prime_oneHundredSixteenDJ_181, prime_oneHundredSixteenDJ_2099, prime_oneHundredSixteenDJ_220917667159773668549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945655 : Nat.totient 137142958555927401591317945655 = 73014815062939113282997128960 := by
  rw [← show ((([(3, 1), (5, 1), (571, 1), (673051521689, 1), (23790185938483, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_571, prime_oneHundredSixteenDJ_673051521689, prime_oneHundredSixteenDJ_23790185938483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945656 : Nat.totient 137142958555927401591317945656 = 68571479277963700795658972824 := by
  rw [← show ((([(2, 3), (17142869819490925198914743207, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_17142869819490925198914743207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945657 : Nat.totient 137142958555927401591317945657 = 137115235997688301588987233552 := by
  rw [← show ((([(5323, 1), (70099, 1), (60015647, 1), (6124078275703, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5323, prime_oneHundredSixteenDJ_70099, prime_oneHundredSixteenDJ_60015647, prime_oneHundredSixteenDJ_6124078275703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945658 : Nat.totient 137142958555927401591317945658 = 40037809559756154624570624000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (29, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_29, prime_oneHundredSixteenDJ_461, prime_oneHundredSixteenDJ_69997, prime_oneHundredSixteenDJ_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945659 : Nat.totient 137142958555927401591317945659 = 114829943213704244508648388800 := by
  rw [← show ((([(7, 1), (83, 1), (89, 1), (2652206744588512668806551, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_83, prime_oneHundredSixteenDJ_89, prime_oneHundredSixteenDJ_2652206744588512668806551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945660 : Nat.totient 137142958555927401591317945660 = 54854232048646186818232709504 := by
  rw [← show ((([(2, 2), (5, 1), (18587, 1), (368921715596727286790009, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_18587, prime_oneHundredSixteenDJ_368921715596727286790009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945661 : Nat.totient 137142958555927401591317945661 = 84395666803647631748503351104 := by
  rw [← show ((([(3, 2), (13, 1), (1172162038939550440951435433, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_1172162038939550440951435433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945662 : Nat.totient 137142958555927401591317945662 = 64358091644138305449374825728 := by
  rw [← show ((([(2, 1), (17, 1), (359, 1), (11235700356867720923424377, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_17, prime_oneHundredSixteenDJ_359, prime_oneHundredSixteenDJ_11235700356867720923424377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945663 : Nat.totient 137142958555927401591317945663 = 134894713310956748262704777280 := by
  rw [← show ((([(61, 1), (5931436409, 1), (379038915230881987, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_61, prime_oneHundredSixteenDJ_5931436409, prime_oneHundredSixteenDJ_379038915230881987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945664 : Nat.totient 137142958555927401591317945664 = 45714268605721882665255579648 := by
  rw [← show ((([(2, 6), (3, 1), (899893, 1), (403945337, 1), (1964983069187, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_899893, prime_oneHundredSixteenDJ_403945337, prime_oneHundredSixteenDJ_1964983069187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945665 : Nat.totient 137142958555927401591317945665 = 109424883027209620689220438512 := by
  rw [← show ((([(5, 1), (379, 1), (72370954383075145958479127, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_379, prime_oneHundredSixteenDJ_72370954383075145958479127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945666 : Nat.totient 137142958555927401591317945666 = 56220094811746636677186238464 := by
  rw [← show ((([(2, 1), (7, 1), (23, 1), (425909809179898762705956353, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_23, prime_oneHundredSixteenDJ_425909809179898762705956353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945667 : Nat.totient 137142958555927401591317945667 = 91428639037284934394211963776 := by
  rw [← show ((([(3, 1), (45714319518642467197105981889, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_45714319518642467197105981889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945668 : Nat.totient 137142958555927401591317945668 = 68364314688000064237363929960 := by
  rw [← show ((([(2, 2), (331, 1), (103582294981818279147521107, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_331, prime_oneHundredSixteenDJ_103582294981818279147521107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945669 : Nat.totient 137142958555927401591317945669 = 124675416869024910537561768680 := by
  rw [← show ((([(11, 2), (1133412880627499186705106989, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_1133412880627499186705106989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945670 : Nat.totient 137142958555927401591317945670 = 36571455614913973757684785440 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (507936883540471857745622021, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_507936883540471857745622021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945671 : Nat.totient 137142958555927401591317945671 = 133285288914332168576925093120 := by
  rw [← show ((([(41, 1), (479, 1), (587, 1), (22469, 1), (529458955499661463, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_41, prime_oneHundredSixteenDJ_479, prime_oneHundredSixteenDJ_587, prime_oneHundredSixteenDJ_22469, prime_oneHundredSixteenDJ_529458955499661463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945672 : Nat.totient 137142958555927401591317945672 = 68570963817090578698505713920 := by
  rw [← show ((([(2, 3), (133073, 1), (406538471, 1), (316877884485823, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_133073, prime_oneHundredSixteenDJ_406538471, prime_oneHundredSixteenDJ_316877884485823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945673 : Nat.totient 137142958555927401591317945673 = 74187917697892782929240148480 := by
  rw [← show ((([(3, 1), (7, 1), (19, 1), (1381, 1), (65843, 1), (3780048129433800569, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_19, prime_oneHundredSixteenDJ_1381, prime_oneHundredSixteenDJ_65843, prime_oneHundredSixteenDJ_3780048129433800569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945674 : Nat.totient 137142958555927401591317945674 = 63296750095140606458401728432 := by
  rw [← show ((([(2, 1), (13, 1), (8333873987, 1), (632926437747441427, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_8333873987, prime_oneHundredSixteenDJ_632926437747441427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945675 : Nat.totient 137142958555927401591317945675 = 109714366844653308326723217600 := by
  rw [← show ((([(5, 2), (1238476406267, 1), (4429408840150681, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_1238476406267, prime_oneHundredSixteenDJ_4429408840150681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945676 : Nat.totient 137142958555927401591317945676 = 45710447720597354766581914512 := by
  rw [← show ((([(2, 2), (3, 1), (11807, 1), (967949511278107631005039, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_11807, prime_oneHundredSixteenDJ_967949511278107631005039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945677 : Nat.totient 137142958555927401591317945677 = 137142958497922971354902318620 := by
  rw [← show ((([(2364353171, 1), (58004430234051273887, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2364353171, prime_oneHundredSixteenDJ_58004430234051273887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945678 : Nat.totient 137142958555927401591317945678 = 68246495963850128753973385080 := by
  rw [← show ((([(2, 1), (211, 1), (324983314113572041685587549, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_211, prime_oneHundredSixteenDJ_324983314113572041685587549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945679 : Nat.totient 137142958555927401591317945679 = 85372887360504729843683804160 := by
  rw [← show ((([(3, 2), (17, 1), (127, 1), (2597011, 1), (122424557, 1), (22199133967, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_17, prime_oneHundredSixteenDJ_127, prime_oneHundredSixteenDJ_2597011, prime_oneHundredSixteenDJ_122424557, prime_oneHundredSixteenDJ_22199133967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945680 : Nat.totient 137142958555927401591317945680 = 42745855859642658506021644800 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (11, 1), (31602863, 1), (704476277925837371, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_31602863, prime_oneHundredSixteenDJ_704476277925837371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945681 : Nat.totient 137142958555927401591317945681 = 132525972340066662243374299968 := by
  rw [← show ((([(47, 1), (79, 1), (36935889726885914783549137, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_47, prime_oneHundredSixteenDJ_79, prime_oneHundredSixteenDJ_36935889726885914783549137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945682 : Nat.totient 137142958555927401591317945682 = 43921393059876594835647738240 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (139, 1), (1687213519, 1), (3143950669812857, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_31, prime_oneHundredSixteenDJ_139, prime_oneHundredSixteenDJ_1687213519, prime_oneHundredSixteenDJ_3143950669812857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945683 : Nat.totient 137142958555927401591317945683 = 133669897447554132661365707520 := by
  rw [← show ((([(71, 1), (97, 1), (907, 1), (21955136630064473066687, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_71, prime_oneHundredSixteenDJ_97, prime_oneHundredSixteenDJ_907, prime_oneHundredSixteenDJ_21955136630064473066687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945684 : Nat.totient 137142958555927401591317945684 = 68470191821122529054803239456 := by
  rw [← show ((([(2, 2), (677, 1), (359326039, 1), (140940615619369207, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_677, prime_oneHundredSixteenDJ_359326039, prime_oneHundredSixteenDJ_140940615619369207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945685 : Nat.totient 137142958555927401591317945685 = 73142911228038895512766179072 := by
  rw [← show ((([(3, 1), (5, 1), (40883621323, 1), (223631459441802673, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_40883621323, prime_oneHundredSixteenDJ_223631459441802673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945686 : Nat.totient 137142958555927401591317945686 = 68571479277963700795658972842 := by
  rw [← show ((([(2, 1), (68571479277963700795658972843, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_68571479277963700795658972843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945687 : Nat.totient 137142958555927401591317945687 = 102595413487277806689226752000 := by
  rw [← show ((([(7, 1), (13, 1), (29, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_29, prime_oneHundredSixteenDJ_101, prime_oneHundredSixteenDJ_103, prime_oneHundredSixteenDJ_1163, prime_oneHundredSixteenDJ_3221, prime_oneHundredSixteenDJ_20357, prime_oneHundredSixteenDJ_53279, prime_oneHundredSixteenDJ_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945688 : Nat.totient 137142958555927401591317945688 = 44444516607445514010797998080 := by
  rw [← show ((([(2, 3), (3, 2), (37, 1), (2393, 1), (2833, 1), (2564843623, 1), (2960664041, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_37, prime_oneHundredSixteenDJ_2393, prime_oneHundredSixteenDJ_2833, prime_oneHundredSixteenDJ_2564843623, prime_oneHundredSixteenDJ_2960664041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945689 : Nat.totient 137142958555927401591317945689 = 131180205510556431705101127216 := by
  rw [← show ((([(23, 1), (8346469, 1), (714402381236734082147, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_23, prime_oneHundredSixteenDJ_8346469, prime_oneHundredSixteenDJ_714402381236734082147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945690 : Nat.totient 137142958555927401591317945690 = 54857183398346848363679986176 := by
  rw [← show ((([(2, 1), (5, 1), (2283421873, 1), (6006028065928376153, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_2283421873, prime_oneHundredSixteenDJ_6006028065928376153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945691 : Nat.totient 137142958555927401591317945691 = 81374077856763197481388707840 := by
  rw [← show ((([(3, 1), (11, 1), (53, 1), (467, 1), (167029617749, 1), (1005248275873, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_11, prime_oneHundredSixteenDJ_53, prime_oneHundredSixteenDJ_467, prime_oneHundredSixteenDJ_167029617749, prime_oneHundredSixteenDJ_1005248275873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945692 : Nat.totient 137142958555927401591317945692 = 63861395509539789144217631856 := by
  rw [← show ((([(2, 2), (19, 1), (59, 1), (30584959535220205528839863, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_19, prime_oneHundredSixteenDJ_59, prime_oneHundredSixteenDJ_30584959535220205528839863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945693 : Nat.totient 137142958555927401591317945693 = 137126215428280480897679637180 := by
  rw [← show ((([(8191, 1), (16743127646920693638300323, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_8191, prime_oneHundredSixteenDJ_16743127646920693638300323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945694 : Nat.totient 137142958555927401591317945694 = 38646939397147364447306537472 := by
  rw [← show ((([(2, 1), (3, 1), (7, 3), (73, 1), (184119856867, 1), (4957978681273, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_73, prime_oneHundredSixteenDJ_184119856867, prime_oneHundredSixteenDJ_4957978681273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945695 : Nat.totient 137142958555927401591317945695 = 109646178922261256293346759424 := by
  rw [← show ((([(5, 1), (1609, 1), (417736982447, 1), (40807927643893, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_1609, prime_oneHundredSixteenDJ_417736982447, prime_oneHundredSixteenDJ_40807927643893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945696 : Nat.totient 137142958555927401591317945696 = 64362010361942015585459251200 := by
  rw [← show ((([(2, 5), (17, 1), (367, 1), (113666263027, 1), (6043339160951, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_17, prime_oneHundredSixteenDJ_367, prime_oneHundredSixteenDJ_113666263027, prime_oneHundredSixteenDJ_6043339160951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945697 : Nat.totient 137142958555927401591317945697 = 88767646757826286394157235488 := by
  rw [← show ((([(3, 4), (43, 1), (167, 1), (235778156960716640089877, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_43, prime_oneHundredSixteenDJ_167, prime_oneHundredSixteenDJ_235778156960716640089877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945698 : Nat.totient 137142958555927401591317945698 = 68557578541363342811712470256 := by
  rw [← show ((([(2, 1), (4933, 1), (395840099, 1), (35116612592658847, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_4933, prime_oneHundredSixteenDJ_395840099, prime_oneHundredSixteenDJ_35116612592658847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945699 : Nat.totient 137142958555927401591317945699 = 137131641406053054088929659520 := by
  rw [← show ((([(14519, 1), (101221, 1), (309223, 1), (1897669, 1), (159028123, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_14519, prime_oneHundredSixteenDJ_101221, prime_oneHundredSixteenDJ_309223, prime_oneHundredSixteenDJ_1897669, prime_oneHundredSixteenDJ_159028123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945700 : Nat.totient 137142958555927401591317945700 = 33617918088655980512174899200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (13, 1), (241, 1), (123217, 1), (1184189576153641879, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_2, prime_oneHundredSixteenDJ_3, prime_oneHundredSixteenDJ_5, prime_oneHundredSixteenDJ_13, prime_oneHundredSixteenDJ_241, prime_oneHundredSixteenDJ_123217, prime_oneHundredSixteenDJ_1184189576153641879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixteenDJ_137142958555927401591317945701 : Nat.totient 137142958555927401591317945701 = 117344514877881141005074452768 := by
  rw [← show ((([(7, 1), (569, 1), (34432075961819583628249547, 1)] : List FactorBlock).map factorBlockValue).prod) = 137142958555927401591317945701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixteenDJ_7, prime_oneHundredSixteenDJ_569, prime_oneHundredSixteenDJ_34432075961819583628249547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixteenDJ : certifiedKill 1 137142958555927401591317945599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixteenDJ_137142958555927401591317945600, phi_oneHundredSixteenDJ_137142958555927401591317945601, phi_oneHundredSixteenDJ_137142958555927401591317945602,
    phi_oneHundredSixteenDJ_137142958555927401591317945603, phi_oneHundredSixteenDJ_137142958555927401591317945604, phi_oneHundredSixteenDJ_137142958555927401591317945605,
    phi_oneHundredSixteenDJ_137142958555927401591317945606, phi_oneHundredSixteenDJ_137142958555927401591317945607, phi_oneHundredSixteenDJ_137142958555927401591317945608,
    phi_oneHundredSixteenDJ_137142958555927401591317945609, phi_oneHundredSixteenDJ_137142958555927401591317945610, phi_oneHundredSixteenDJ_137142958555927401591317945611,
    phi_oneHundredSixteenDJ_137142958555927401591317945612, phi_oneHundredSixteenDJ_137142958555927401591317945613, phi_oneHundredSixteenDJ_137142958555927401591317945614,
    phi_oneHundredSixteenDJ_137142958555927401591317945615, phi_oneHundredSixteenDJ_137142958555927401591317945616, phi_oneHundredSixteenDJ_137142958555927401591317945617,
    phi_oneHundredSixteenDJ_137142958555927401591317945618, phi_oneHundredSixteenDJ_137142958555927401591317945619, phi_oneHundredSixteenDJ_137142958555927401591317945620,
    phi_oneHundredSixteenDJ_137142958555927401591317945621, phi_oneHundredSixteenDJ_137142958555927401591317945622, phi_oneHundredSixteenDJ_137142958555927401591317945623,
    phi_oneHundredSixteenDJ_137142958555927401591317945624, phi_oneHundredSixteenDJ_137142958555927401591317945625, phi_oneHundredSixteenDJ_137142958555927401591317945626,
    phi_oneHundredSixteenDJ_137142958555927401591317945627, phi_oneHundredSixteenDJ_137142958555927401591317945628, phi_oneHundredSixteenDJ_137142958555927401591317945629,
    phi_oneHundredSixteenDJ_137142958555927401591317945630, phi_oneHundredSixteenDJ_137142958555927401591317945631, phi_oneHundredSixteenDJ_137142958555927401591317945632,
    phi_oneHundredSixteenDJ_137142958555927401591317945633, phi_oneHundredSixteenDJ_137142958555927401591317945634, phi_oneHundredSixteenDJ_137142958555927401591317945635,
    phi_oneHundredSixteenDJ_137142958555927401591317945636, phi_oneHundredSixteenDJ_137142958555927401591317945637, phi_oneHundredSixteenDJ_137142958555927401591317945638,
    phi_oneHundredSixteenDJ_137142958555927401591317945639, phi_oneHundredSixteenDJ_137142958555927401591317945640, phi_oneHundredSixteenDJ_137142958555927401591317945641,
    phi_oneHundredSixteenDJ_137142958555927401591317945642, phi_oneHundredSixteenDJ_137142958555927401591317945643, phi_oneHundredSixteenDJ_137142958555927401591317945644,
    phi_oneHundredSixteenDJ_137142958555927401591317945645, phi_oneHundredSixteenDJ_137142958555927401591317945646, phi_oneHundredSixteenDJ_137142958555927401591317945647,
    phi_oneHundredSixteenDJ_137142958555927401591317945648, phi_oneHundredSixteenDJ_137142958555927401591317945649, phi_oneHundredSixteenDJ_137142958555927401591317945650,
    phi_oneHundredSixteenDJ_137142958555927401591317945651, phi_oneHundredSixteenDJ_137142958555927401591317945652, phi_oneHundredSixteenDJ_137142958555927401591317945653,
    phi_oneHundredSixteenDJ_137142958555927401591317945654, phi_oneHundredSixteenDJ_137142958555927401591317945655, phi_oneHundredSixteenDJ_137142958555927401591317945656,
    phi_oneHundredSixteenDJ_137142958555927401591317945657, phi_oneHundredSixteenDJ_137142958555927401591317945658, phi_oneHundredSixteenDJ_137142958555927401591317945659,
    phi_oneHundredSixteenDJ_137142958555927401591317945660, phi_oneHundredSixteenDJ_137142958555927401591317945661, phi_oneHundredSixteenDJ_137142958555927401591317945662,
    phi_oneHundredSixteenDJ_137142958555927401591317945663, phi_oneHundredSixteenDJ_137142958555927401591317945664, phi_oneHundredSixteenDJ_137142958555927401591317945665,
    phi_oneHundredSixteenDJ_137142958555927401591317945666, phi_oneHundredSixteenDJ_137142958555927401591317945667, phi_oneHundredSixteenDJ_137142958555927401591317945668,
    phi_oneHundredSixteenDJ_137142958555927401591317945669, phi_oneHundredSixteenDJ_137142958555927401591317945670, phi_oneHundredSixteenDJ_137142958555927401591317945671,
    phi_oneHundredSixteenDJ_137142958555927401591317945672, phi_oneHundredSixteenDJ_137142958555927401591317945673, phi_oneHundredSixteenDJ_137142958555927401591317945674,
    phi_oneHundredSixteenDJ_137142958555927401591317945675, phi_oneHundredSixteenDJ_137142958555927401591317945676, phi_oneHundredSixteenDJ_137142958555927401591317945677,
    phi_oneHundredSixteenDJ_137142958555927401591317945678, phi_oneHundredSixteenDJ_137142958555927401591317945679, phi_oneHundredSixteenDJ_137142958555927401591317945680,
    phi_oneHundredSixteenDJ_137142958555927401591317945681, phi_oneHundredSixteenDJ_137142958555927401591317945682, phi_oneHundredSixteenDJ_137142958555927401591317945683,
    phi_oneHundredSixteenDJ_137142958555927401591317945684, phi_oneHundredSixteenDJ_137142958555927401591317945685, phi_oneHundredSixteenDJ_137142958555927401591317945686,
    phi_oneHundredSixteenDJ_137142958555927401591317945687, phi_oneHundredSixteenDJ_137142958555927401591317945688, phi_oneHundredSixteenDJ_137142958555927401591317945689,
    phi_oneHundredSixteenDJ_137142958555927401591317945690, phi_oneHundredSixteenDJ_137142958555927401591317945691, phi_oneHundredSixteenDJ_137142958555927401591317945692,
    phi_oneHundredSixteenDJ_137142958555927401591317945693, phi_oneHundredSixteenDJ_137142958555927401591317945694, phi_oneHundredSixteenDJ_137142958555927401591317945695,
    phi_oneHundredSixteenDJ_137142958555927401591317945696, phi_oneHundredSixteenDJ_137142958555927401591317945697, phi_oneHundredSixteenDJ_137142958555927401591317945698,
    phi_oneHundredSixteenDJ_137142958555927401591317945699, phi_oneHundredSixteenDJ_137142958555927401591317945700, phi_oneHundredSixteenDJ_137142958555927401591317945701]

end TotientTailPeriodKiller
end Erdos249257
