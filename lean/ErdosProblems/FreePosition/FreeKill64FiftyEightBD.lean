import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 58P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyEightBDFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyEightBDFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyEightBDFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyEightBDFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyEightBDFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyEightBDFastPow a n * fiftyEightBDFastPow a n * a
        else fiftyEightBDFastPow a n * fiftyEightBDFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyEightBD_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyEightBD_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyEightBD_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyEightBD_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyEightBD_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyEightBD_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyEightBD_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyEightBD_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyEightBD_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyEightBD_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyEightBD_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyEightBD_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyEightBD_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyEightBD_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyEightBD_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyEightBD_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyEightBD_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyEightBD_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyEightBD_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyEightBD_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyEightBD_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyEightBD_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyEightBD_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyEightBD_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyEightBD_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyEightBD_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyEightBD_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyEightBD_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyEightBD_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyEightBD_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyEightBD_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyEightBD_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyEightBD_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyEightBD_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftyEightBD_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyEightBD_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyEightBD_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyEightBD_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyEightBD_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyEightBD_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyEightBD_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyEightBD_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyEightBD_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyEightBD_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftyEightBD_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyEightBD_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyEightBD_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyEightBD_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyEightBD_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftyEightBD_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftyEightBD_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyEightBD_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftyEightBD_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftyEightBD_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyEightBD_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftyEightBD_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyEightBD_281 : Nat.Prime 281 := by norm_num
private theorem prime_fiftyEightBD_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyEightBD_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftyEightBD_331 : Nat.Prime 331 := by norm_num
private theorem prime_fiftyEightBD_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftyEightBD_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftyEightBD_367 : Nat.Prime 367 := by norm_num
private theorem prime_fiftyEightBD_379 : Nat.Prime 379 := by norm_num
private theorem prime_fiftyEightBD_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyEightBD_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftyEightBD_401 : Nat.Prime 401 := by norm_num
private theorem prime_fiftyEightBD_409 : Nat.Prime 409 := by norm_num
private theorem prime_fiftyEightBD_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyEightBD_431 : Nat.Prime 431 := by norm_num
private theorem prime_fiftyEightBD_433 : Nat.Prime 433 := by norm_num
private theorem prime_fiftyEightBD_443 : Nat.Prime 443 := by norm_num
private theorem prime_fiftyEightBD_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftyEightBD_467 : Nat.Prime 467 := by norm_num
private theorem prime_fiftyEightBD_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyEightBD_491 : Nat.Prime 491 := by norm_num
private theorem prime_fiftyEightBD_499 : Nat.Prime 499 := by norm_num
private theorem prime_fiftyEightBD_503 : Nat.Prime 503 := by norm_num
private theorem prime_fiftyEightBD_523 : Nat.Prime 523 := by norm_num
private theorem prime_fiftyEightBD_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyEightBD_563 : Nat.Prime 563 := by norm_num
private theorem prime_fiftyEightBD_571 : Nat.Prime 571 := by norm_num
private theorem prime_fiftyEightBD_587 : Nat.Prime 587 := by norm_num
private theorem prime_fiftyEightBD_601 : Nat.Prime 601 := by norm_num
private theorem prime_fiftyEightBD_617 : Nat.Prime 617 := by norm_num
private theorem prime_fiftyEightBD_641 : Nat.Prime 641 := by norm_num
private theorem prime_fiftyEightBD_661 : Nat.Prime 661 := by norm_num
private theorem prime_fiftyEightBD_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftyEightBD_683 : Nat.Prime 683 := by norm_num
private theorem prime_fiftyEightBD_757 : Nat.Prime 757 := by norm_num
private theorem prime_fiftyEightBD_769 : Nat.Prime 769 := by norm_num
private theorem prime_fiftyEightBD_787 : Nat.Prime 787 := by norm_num
private theorem prime_fiftyEightBD_811 : Nat.Prime 811 := by norm_num
private theorem prime_fiftyEightBD_829 : Nat.Prime 829 := by norm_num
private theorem prime_fiftyEightBD_839 : Nat.Prime 839 := by norm_num
private theorem prime_fiftyEightBD_887 : Nat.Prime 887 := by norm_num
private theorem prime_fiftyEightBD_911 : Nat.Prime 911 := by norm_num
private theorem prime_fiftyEightBD_937 : Nat.Prime 937 := by norm_num
private theorem prime_fiftyEightBD_953 : Nat.Prime 953 := by norm_num
private theorem prime_fiftyEightBD_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_fiftyEightBD_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_fiftyEightBD_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fiftyEightBD_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fiftyEightBD_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fiftyEightBD_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_fiftyEightBD_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_fiftyEightBD_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_fiftyEightBD_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fiftyEightBD_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fiftyEightBD_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_fiftyEightBD_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_fiftyEightBD_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fiftyEightBD_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_fiftyEightBD_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_fiftyEightBD_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_fiftyEightBD_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_fiftyEightBD_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_fiftyEightBD_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fiftyEightBD_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_fiftyEightBD_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_fiftyEightBD_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_fiftyEightBD_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_fiftyEightBD_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fiftyEightBD_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fiftyEightBD_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_fiftyEightBD_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_fiftyEightBD_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fiftyEightBD_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_fiftyEightBD_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_fiftyEightBD_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_fiftyEightBD_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_fiftyEightBD_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_fiftyEightBD_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_fiftyEightBD_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_fiftyEightBD_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_fiftyEightBD_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_fiftyEightBD_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_fiftyEightBD_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_fiftyEightBD_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_fiftyEightBD_2503 : Nat.Prime 2503 := by norm_num
private theorem prime_fiftyEightBD_2543 : Nat.Prime 2543 := by norm_num
private theorem prime_fiftyEightBD_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_fiftyEightBD_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_fiftyEightBD_2711 : Nat.Prime 2711 := by norm_num
private theorem prime_fiftyEightBD_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_fiftyEightBD_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fiftyEightBD_3083 : Nat.Prime 3083 := by norm_num
private theorem prime_fiftyEightBD_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_fiftyEightBD_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_fiftyEightBD_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_fiftyEightBD_3373 : Nat.Prime 3373 := by norm_num
private theorem prime_fiftyEightBD_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_fiftyEightBD_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_fiftyEightBD_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_fiftyEightBD_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_fiftyEightBD_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_fiftyEightBD_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_fiftyEightBD_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_fiftyEightBD_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_fiftyEightBD_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_fiftyEightBD_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_fiftyEightBD_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_fiftyEightBD_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_fiftyEightBD_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_fiftyEightBD_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_fiftyEightBD_4567 : Nat.Prime 4567 := by norm_num
private theorem prime_fiftyEightBD_4597 : Nat.Prime 4597 := by norm_num
private theorem prime_fiftyEightBD_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_fiftyEightBD_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_fiftyEightBD_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_fiftyEightBD_5407 : Nat.Prime 5407 := by norm_num
private theorem prime_fiftyEightBD_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_fiftyEightBD_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_fiftyEightBD_5867 : Nat.Prime 5867 := by norm_num
private theorem prime_fiftyEightBD_5923 : Nat.Prime 5923 := by norm_num
private theorem prime_fiftyEightBD_6329 : Nat.Prime 6329 := by norm_num
private theorem prime_fiftyEightBD_6361 : Nat.Prime 6361 := by norm_num
private theorem prime_fiftyEightBD_6569 : Nat.Prime 6569 := by norm_num
private theorem prime_fiftyEightBD_6581 : Nat.Prime 6581 := by norm_num
private theorem prime_fiftyEightBD_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_fiftyEightBD_6679 : Nat.Prime 6679 := by norm_num
private theorem prime_fiftyEightBD_6791 : Nat.Prime 6791 := by norm_num
private theorem prime_fiftyEightBD_6803 : Nat.Prime 6803 := by norm_num
private theorem prime_fiftyEightBD_6829 : Nat.Prime 6829 := by norm_num
private theorem prime_fiftyEightBD_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_fiftyEightBD_7547 : Nat.Prime 7547 := by norm_num
private theorem prime_fiftyEightBD_7789 : Nat.Prime 7789 := by norm_num
private theorem prime_fiftyEightBD_8009 : Nat.Prime 8009 := by norm_num
private theorem prime_fiftyEightBD_8317 : Nat.Prime 8317 := by norm_num
private theorem prime_fiftyEightBD_8329 : Nat.Prime 8329 := by norm_num
private theorem prime_fiftyEightBD_8467 : Nat.Prime 8467 := by norm_num
private theorem prime_fiftyEightBD_8527 : Nat.Prime 8527 := by norm_num
private theorem prime_fiftyEightBD_8647 : Nat.Prime 8647 := by norm_num
private theorem prime_fiftyEightBD_8893 : Nat.Prime 8893 := by norm_num
private theorem prime_fiftyEightBD_9173 : Nat.Prime 9173 := by norm_num
private theorem prime_fiftyEightBD_9521 : Nat.Prime 9521 := by norm_num
private theorem prime_fiftyEightBD_9743 : Nat.Prime 9743 := by norm_num
private theorem prime_fiftyEightBD_9749 : Nat.Prime 9749 := by norm_num
private theorem prime_fiftyEightBD_10289 : Nat.Prime 10289 := by norm_num
private theorem prime_fiftyEightBD_10979 : Nat.Prime 10979 := by norm_num
private theorem prime_fiftyEightBD_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_fiftyEightBD_11317 : Nat.Prime 11317 := by norm_num
private theorem prime_fiftyEightBD_11593 : Nat.Prime 11593 := by norm_num
private theorem prime_fiftyEightBD_11719 : Nat.Prime 11719 := by norm_num
private theorem prime_fiftyEightBD_11731 : Nat.Prime 11731 := by norm_num
private theorem prime_fiftyEightBD_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_fiftyEightBD_12157 : Nat.Prime 12157 := by norm_num
private theorem prime_fiftyEightBD_12211 : Nat.Prime 12211 := by norm_num
private theorem prime_fiftyEightBD_12413 : Nat.Prime 12413 := by norm_num
private theorem prime_fiftyEightBD_13313 : Nat.Prime 13313 := by norm_num
private theorem prime_fiftyEightBD_13921 : Nat.Prime 13921 := by norm_num
private theorem prime_fiftyEightBD_14551 : Nat.Prime 14551 := by norm_num
private theorem prime_fiftyEightBD_14621 : Nat.Prime 14621 := by norm_num
private theorem prime_fiftyEightBD_15401 : Nat.Prime 15401 := by norm_num
private theorem prime_fiftyEightBD_15439 : Nat.Prime 15439 := by norm_num
private theorem prime_fiftyEightBD_15901 : Nat.Prime 15901 := by norm_num
private theorem prime_fiftyEightBD_16871 : Nat.Prime 16871 := by norm_num
private theorem prime_fiftyEightBD_17027 : Nat.Prime 17027 := by norm_num
private theorem prime_fiftyEightBD_18443 : Nat.Prime 18443 := by norm_num
private theorem prime_fiftyEightBD_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_fiftyEightBD_19267 : Nat.Prime 19267 := by norm_num
private theorem prime_fiftyEightBD_19571 : Nat.Prime 19571 := by norm_num
private theorem prime_fiftyEightBD_19961 : Nat.Prime 19961 := by norm_num
private theorem prime_fiftyEightBD_20023 : Nat.Prime 20023 := by norm_num
private theorem prime_fiftyEightBD_20051 : Nat.Prime 20051 := by norm_num
private theorem prime_fiftyEightBD_20731 : Nat.Prime 20731 := by norm_num
private theorem prime_fiftyEightBD_20857 : Nat.Prime 20857 := by norm_num
private theorem prime_fiftyEightBD_20939 : Nat.Prime 20939 := by norm_num
private theorem prime_fiftyEightBD_21067 : Nat.Prime 21067 := by norm_num
private theorem prime_fiftyEightBD_21803 : Nat.Prime 21803 := by norm_num
private theorem prime_fiftyEightBD_22123 : Nat.Prime 22123 := by norm_num
private theorem prime_fiftyEightBD_22391 : Nat.Prime 22391 := by norm_num
private theorem prime_fiftyEightBD_25073 : Nat.Prime 25073 := by norm_num
private theorem prime_fiftyEightBD_25117 : Nat.Prime 25117 := by norm_num
private theorem prime_fiftyEightBD_25189 : Nat.Prime 25189 := by norm_num
private theorem prime_fiftyEightBD_25247 : Nat.Prime 25247 := by norm_num
private theorem prime_fiftyEightBD_25633 : Nat.Prime 25633 := by norm_num
private theorem prime_fiftyEightBD_25741 : Nat.Prime 25741 := by norm_num
private theorem prime_fiftyEightBD_26437 : Nat.Prime 26437 := by norm_num
private theorem prime_fiftyEightBD_26539 : Nat.Prime 26539 := by norm_num
private theorem prime_fiftyEightBD_27509 : Nat.Prime 27509 := by norm_num
private theorem prime_fiftyEightBD_28111 : Nat.Prime 28111 := by norm_num
private theorem prime_fiftyEightBD_28123 : Nat.Prime 28123 := by norm_num
private theorem prime_fiftyEightBD_28621 : Nat.Prime 28621 := by norm_num
private theorem prime_fiftyEightBD_29243 : Nat.Prime 29243 := by norm_num
private theorem prime_fiftyEightBD_29303 : Nat.Prime 29303 := by norm_num
private theorem prime_fiftyEightBD_30367 : Nat.Prime 30367 := by norm_num
private theorem prime_fiftyEightBD_31481 : Nat.Prime 31481 := by norm_num
private theorem prime_fiftyEightBD_31727 : Nat.Prime 31727 := by norm_num
private theorem prime_fiftyEightBD_34273 : Nat.Prime 34273 := by norm_num
private theorem prime_fiftyEightBD_34757 : Nat.Prime 34757 := by norm_num
private theorem prime_fiftyEightBD_36209 : Nat.Prime 36209 := by norm_num
private theorem prime_fiftyEightBD_36343 : Nat.Prime 36343 := by norm_num
private theorem prime_fiftyEightBD_37003 : Nat.Prime 37003 := by norm_num
private theorem prime_fiftyEightBD_37181 : Nat.Prime 37181 := by norm_num
private theorem prime_fiftyEightBD_37223 : Nat.Prime 37223 := by norm_num
private theorem prime_fiftyEightBD_37501 : Nat.Prime 37501 := by norm_num
private theorem prime_fiftyEightBD_38149 : Nat.Prime 38149 := by norm_num
private theorem prime_fiftyEightBD_39359 : Nat.Prime 39359 := by norm_num
private theorem prime_fiftyEightBD_41609 : Nat.Prime 41609 := by norm_num
private theorem prime_fiftyEightBD_41611 : Nat.Prime 41611 := by norm_num
private theorem prime_fiftyEightBD_41621 : Nat.Prime 41621 := by norm_num
private theorem prime_fiftyEightBD_41777 : Nat.Prime 41777 := by norm_num
private theorem prime_fiftyEightBD_42533 : Nat.Prime 42533 := by norm_num
private theorem prime_fiftyEightBD_43783 : Nat.Prime 43783 := by norm_num
private theorem prime_fiftyEightBD_44953 : Nat.Prime 44953 := by norm_num
private theorem prime_fiftyEightBD_45121 : Nat.Prime 45121 := by norm_num
private theorem prime_fiftyEightBD_45161 : Nat.Prime 45161 := by norm_num
private theorem prime_fiftyEightBD_45341 : Nat.Prime 45341 := by norm_num
private theorem prime_fiftyEightBD_48661 : Nat.Prime 48661 := by norm_num
private theorem prime_fiftyEightBD_52259 : Nat.Prime 52259 := by norm_num
private theorem prime_fiftyEightBD_52673 : Nat.Prime 52673 := by norm_num
private theorem prime_fiftyEightBD_52709 : Nat.Prime 52709 := by norm_num
private theorem prime_fiftyEightBD_53987 : Nat.Prime 53987 := by norm_num
private theorem prime_fiftyEightBD_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_fiftyEightBD_61933 : Nat.Prime 61933 := by norm_num
private theorem prime_fiftyEightBD_64783 : Nat.Prime 64783 := by norm_num
private theorem prime_fiftyEightBD_65557 : Nat.Prime 65557 := by norm_num
private theorem prime_fiftyEightBD_69499 : Nat.Prime 69499 := by norm_num
private theorem prime_fiftyEightBD_70459 : Nat.Prime 70459 := by norm_num
private theorem prime_fiftyEightBD_74219 : Nat.Prime 74219 := by norm_num
private theorem prime_fiftyEightBD_79393 : Nat.Prime 79393 := by norm_num
private theorem prime_fiftyEightBD_79813 : Nat.Prime 79813 := by norm_num
private theorem prime_fiftyEightBD_80287 : Nat.Prime 80287 := by norm_num
private theorem prime_fiftyEightBD_82759 : Nat.Prime 82759 := by norm_num
private theorem prime_fiftyEightBD_84659 : Nat.Prime 84659 := by norm_num
private theorem prime_fiftyEightBD_96959 : Nat.Prime 96959 := by norm_num
private theorem prime_fiftyEightBD_110923 : Nat.Prime 110923 := by norm_num
private theorem prime_fiftyEightBD_111431 : Nat.Prime 111431 := by norm_num
private theorem prime_fiftyEightBD_113363 : Nat.Prime 113363 := by norm_num
private theorem prime_fiftyEightBD_115933 : Nat.Prime 115933 := by norm_num
private theorem prime_fiftyEightBD_116107 : Nat.Prime 116107 := by norm_num
private theorem prime_fiftyEightBD_120833 : Nat.Prime 120833 := by norm_num
private theorem prime_fiftyEightBD_124087 : Nat.Prime 124087 := by norm_num
private theorem prime_fiftyEightBD_125287 : Nat.Prime 125287 := by norm_num
private theorem prime_fiftyEightBD_128959 : Nat.Prime 128959 := by norm_num
private theorem prime_fiftyEightBD_132173 : Nat.Prime 132173 := by norm_num
private theorem prime_fiftyEightBD_135059 : Nat.Prime 135059 := by norm_num
private theorem prime_fiftyEightBD_141959 : Nat.Prime 141959 := by norm_num
private theorem prime_fiftyEightBD_142981 : Nat.Prime 142981 := by norm_num
private theorem prime_fiftyEightBD_151243 : Nat.Prime 151243 := by norm_num
private theorem prime_fiftyEightBD_153887 : Nat.Prime 153887 := by norm_num
private theorem prime_fiftyEightBD_169843 : Nat.Prime 169843 := by norm_num
private theorem prime_fiftyEightBD_180773 : Nat.Prime 180773 := by norm_num
private theorem prime_fiftyEightBD_182111 : Nat.Prime 182111 := by norm_num
private theorem prime_fiftyEightBD_183943 : Nat.Prime 183943 := by norm_num
private theorem prime_fiftyEightBD_186299 : Nat.Prime 186299 := by norm_num
private theorem prime_fiftyEightBD_194521 : Nat.Prime 194521 := by norm_num
private theorem prime_fiftyEightBD_196337 : Nat.Prime 196337 := by norm_num
private theorem prime_fiftyEightBD_201757 : Nat.Prime 201757 := by norm_num
private theorem prime_fiftyEightBD_204857 : Nat.Prime 204857 := by norm_num
private theorem prime_fiftyEightBD_206347 : Nat.Prime 206347 := by norm_num
private theorem prime_fiftyEightBD_208099 : Nat.Prime 208099 := by norm_num
private theorem prime_fiftyEightBD_208367 : Nat.Prime 208367 := by norm_num
private theorem prime_fiftyEightBD_208513 : Nat.Prime 208513 := by norm_num
private theorem prime_fiftyEightBD_225509 : Nat.Prime 225509 := by norm_num
private theorem prime_fiftyEightBD_240811 : Nat.Prime 240811 := by norm_num
private theorem prime_fiftyEightBD_242491 : Nat.Prime 242491 := by norm_num
private theorem prime_fiftyEightBD_271969 : Nat.Prime 271969 := by norm_num
private theorem prime_fiftyEightBD_272249 : Nat.Prime 272249 := by norm_num
private theorem prime_fiftyEightBD_275827 : Nat.Prime 275827 := by norm_num
private theorem prime_fiftyEightBD_276007 : Nat.Prime 276007 := by norm_num
private theorem prime_fiftyEightBD_306331 : Nat.Prime 306331 := by norm_num
private theorem prime_fiftyEightBD_314953 : Nat.Prime 314953 := by norm_num
private theorem prime_fiftyEightBD_324301 : Nat.Prime 324301 := by norm_num
private theorem prime_fiftyEightBD_328961 : Nat.Prime 328961 := by norm_num
private theorem prime_fiftyEightBD_375209 : Nat.Prime 375209 := by norm_num
private theorem prime_fiftyEightBD_411779 : Nat.Prime 411779 := by norm_num
private theorem prime_fiftyEightBD_420319 : Nat.Prime 420319 := by norm_num
private theorem prime_fiftyEightBD_435131 : Nat.Prime 435131 := by norm_num
private theorem prime_fiftyEightBD_464003 : Nat.Prime 464003 := by norm_num
private theorem prime_fiftyEightBD_468667 : Nat.Prime 468667 := by norm_num
private theorem prime_fiftyEightBD_474671 : Nat.Prime 474671 := by norm_num
private theorem prime_fiftyEightBD_521869 : Nat.Prime 521869 := by norm_num
private theorem prime_fiftyEightBD_527809 : Nat.Prime 527809 := by norm_num
private theorem prime_fiftyEightBD_532187 : Nat.Prime 532187 := by norm_num
private theorem prime_fiftyEightBD_543289 : Nat.Prime 543289 := by norm_num
private theorem prime_fiftyEightBD_549683 : Nat.Prime 549683 := by norm_num
private theorem prime_fiftyEightBD_561667 : Nat.Prime 561667 := by norm_num
private theorem prime_fiftyEightBD_570221 : Nat.Prime 570221 := by norm_num
private theorem prime_fiftyEightBD_574711 : Nat.Prime 574711 := by norm_num
private theorem prime_fiftyEightBD_627041 : Nat.Prime 627041 := by norm_num
private theorem prime_fiftyEightBD_628937 : Nat.Prime 628937 := by norm_num
private theorem prime_fiftyEightBD_658403 : Nat.Prime 658403 := by norm_num
private theorem prime_fiftyEightBD_658913 : Nat.Prime 658913 := by norm_num
private theorem prime_fiftyEightBD_719599 : Nat.Prime 719599 := by norm_num
private theorem prime_fiftyEightBD_734017 : Nat.Prime 734017 := by norm_num
private theorem prime_fiftyEightBD_761611 : Nat.Prime 761611 := by norm_num
private theorem prime_fiftyEightBD_802777 : Nat.Prime 802777 := by norm_num
private theorem prime_fiftyEightBD_831239 : Nat.Prime 831239 := by norm_num
private theorem prime_fiftyEightBD_859577 : Nat.Prime 859577 := by norm_num
private theorem prime_fiftyEightBD_878131 : Nat.Prime 878131 := by norm_num
private theorem prime_fiftyEightBD_904181 : Nat.Prime 904181 := by norm_num
private theorem prime_fiftyEightBD_904999 : Nat.Prime 904999 := by norm_num
private theorem prime_fiftyEightBD_953681 : Nat.Prime 953681 := by norm_num
private theorem prime_fiftyEightBD_957557 : Nat.Prime 957557 := by norm_num
private theorem prime_fiftyEightBD_992843 : Nat.Prime 992843 := by norm_num
private theorem prime_fiftyEightBD_1095443 : Nat.Prime 1095443 := by norm_num
private theorem prime_fiftyEightBD_1108057 : Nat.Prime 1108057 := by norm_num
private theorem prime_fiftyEightBD_1168351 : Nat.Prime 1168351 := by norm_num
private theorem prime_fiftyEightBD_1350073 : Nat.Prime 1350073 := by norm_num
private theorem prime_fiftyEightBD_1353827 : Nat.Prime 1353827 := by norm_num
private theorem prime_fiftyEightBD_1464467 : Nat.Prime 1464467 := by norm_num
private theorem prime_fiftyEightBD_1570267 : Nat.Prime 1570267 := by norm_num
private theorem prime_fiftyEightBD_1575557 : Nat.Prime 1575557 := by norm_num
private theorem prime_fiftyEightBD_1618823 : Nat.Prime 1618823 := by norm_num
private theorem prime_fiftyEightBD_1650379 : Nat.Prime 1650379 := by norm_num
private theorem prime_fiftyEightBD_1664543 : Nat.Prime 1664543 := by norm_num
private theorem prime_fiftyEightBD_1680659 : Nat.Prime 1680659 := by norm_num
private theorem prime_fiftyEightBD_1747433 : Nat.Prime 1747433 := by norm_num
private theorem prime_fiftyEightBD_1753069 : Nat.Prime 1753069 := by norm_num
private theorem prime_fiftyEightBD_1768441 : Nat.Prime 1768441 := by norm_num
private theorem prime_fiftyEightBD_1939057 : Nat.Prime 1939057 := by norm_num
private theorem prime_fiftyEightBD_2077939 : Nat.Prime 2077939 := by norm_num
private theorem prime_fiftyEightBD_2103919 : Nat.Prime 2103919 := by norm_num
private theorem prime_fiftyEightBD_2106679 : Nat.Prime 2106679 := by norm_num
private theorem prime_fiftyEightBD_2127919 : Nat.Prime 2127919 := by norm_num
private theorem prime_fiftyEightBD_2144491 : Nat.Prime 2144491 := by norm_num
private theorem prime_fiftyEightBD_2412899 : Nat.Prime 2412899 := by norm_num
private theorem prime_fiftyEightBD_2523581 : Nat.Prime 2523581 := by norm_num
private theorem prime_fiftyEightBD_2603467 : Nat.Prime 2603467 := by norm_num
private theorem prime_fiftyEightBD_2803667 : Nat.Prime 2803667 := by norm_num
private theorem prime_fiftyEightBD_2811131 : Nat.Prime 2811131 := by norm_num
private theorem prime_fiftyEightBD_2999827 : Nat.Prime 2999827 := by norm_num
private theorem prime_fiftyEightBD_3033403 : Nat.Prime 3033403 := by norm_num
private theorem prime_fiftyEightBD_3565591 : Nat.Prime 3565591 := by norm_num
private theorem prime_fiftyEightBD_3712199 : Nat.Prime 3712199 := by norm_num
private theorem prime_fiftyEightBD_3873209 : Nat.Prime 3873209 := by norm_num
private theorem prime_fiftyEightBD_4004579 : Nat.Prime 4004579 := by norm_num
private theorem prime_fiftyEightBD_4289317 : Nat.Prime 4289317 := by norm_num
private theorem prime_fiftyEightBD_4643153 : Nat.Prime 4643153 := by norm_num
private theorem prime_fiftyEightBD_5045483 : Nat.Prime 5045483 := by norm_num
private theorem prime_fiftyEightBD_5097089 : Nat.Prime 5097089 := by norm_num
private theorem prime_fiftyEightBD_5205721 : Nat.Prime 5205721 := by norm_num
private theorem prime_fiftyEightBD_5215663 : Nat.Prime 5215663 := by norm_num
private theorem prime_fiftyEightBD_6165581 : Nat.Prime 6165581 := by norm_num
private theorem prime_fiftyEightBD_6881851 : Nat.Prime 6881851 := by norm_num
private theorem prime_fiftyEightBD_6920761 : Nat.Prime 6920761 := by norm_num
private theorem prime_fiftyEightBD_7041449 : Nat.Prime 7041449 := by norm_num
private theorem prime_fiftyEightBD_7148311 : Nat.Prime 7148311 := by norm_num
private theorem prime_fiftyEightBD_7344247 : Nat.Prime 7344247 := by norm_num
private theorem prime_fiftyEightBD_8476511 : Nat.Prime 8476511 := by norm_num
private theorem prime_fiftyEightBD_8557799 : Nat.Prime 8557799 := by norm_num
private theorem prime_fiftyEightBD_8813107 : Nat.Prime 8813107 := by norm_num
private theorem prime_fiftyEightBD_9028273 : Nat.Prime 9028273 := by norm_num
private theorem prime_fiftyEightBD_9311221 : Nat.Prime 9311221 := by norm_num
private theorem prime_fiftyEightBD_9333109 : Nat.Prime 9333109 := by norm_num
private theorem prime_fiftyEightBD_10008217 : Nat.Prime 10008217 := by norm_num
private theorem prime_fiftyEightBD_10854461 : Nat.Prime 10854461 := by norm_num
private theorem prime_fiftyEightBD_11017217 : Nat.Prime 11017217 := by norm_num
private theorem prime_fiftyEightBD_12360611 : Nat.Prime 12360611 := by norm_num
private theorem prime_fiftyEightBD_12470597 : Nat.Prime 12470597 := by norm_num
private theorem prime_fiftyEightBD_12778151 : Nat.Prime 12778151 := by norm_num
private theorem prime_fiftyEightBD_13183763 : Nat.Prime 13183763 := by norm_num
private theorem prime_fiftyEightBD_13971367 : Nat.Prime 13971367 := by norm_num
private theorem prime_fiftyEightBD_14022119 : Nat.Prime 14022119 := by norm_num
private theorem prime_fiftyEightBD_15479029 : Nat.Prime 15479029 := by norm_num
private theorem prime_fiftyEightBD_16261139 : Nat.Prime 16261139 := by norm_num
private theorem prime_fiftyEightBD_16297927 : Nat.Prime 16297927 := by norm_num
private theorem prime_fiftyEightBD_16881677 : Nat.Prime 16881677 := by norm_num
private theorem prime_fiftyEightBD_18808417 : Nat.Prime 18808417 := by norm_num
private theorem prime_fiftyEightBD_20722283 : Nat.Prime 20722283 := by norm_num
private theorem prime_fiftyEightBD_21847141 : Nat.Prime 21847141 := by norm_num
private theorem prime_fiftyEightBD_23264573 : Nat.Prime 23264573 := by norm_num
private theorem prime_fiftyEightBD_23346599 : Nat.Prime 23346599 := by norm_num
private theorem prime_fiftyEightBD_23592739 : Nat.Prime 23592739 := by norm_num
private theorem prime_fiftyEightBD_23905523 : Nat.Prime 23905523 := by norm_num
private theorem prime_fiftyEightBD_24653459 : Nat.Prime 24653459 := by norm_num
private theorem prime_fiftyEightBD_25332007 : Nat.Prime 25332007 := by norm_num
private theorem prime_fiftyEightBD_25433963 : Nat.Prime 25433963 := by norm_num
private theorem prime_fiftyEightBD_25910077 : Nat.Prime 25910077 := by norm_num
private theorem prime_fiftyEightBD_26465581 : Nat.Prime 26465581 := by norm_num
private theorem prime_fiftyEightBD_32366003 : Nat.Prime 32366003 := by
  apply lucas_primality 32366003 (2 : ZMod 32366003)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (151243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (151243, 1)] : List FactorBlock).map factorBlockValue).prod) = 32366003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_107
      · exact prime_fiftyEightBD_151243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32366003) ^ 16183001 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32366003) ^ 302486 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32366003) ^ 214 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_33733573 : Nat.Prime 33733573 := by
  apply lucas_primality 33733573 (5 : ZMod 33733573)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2811131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2811131, 1)] : List FactorBlock).map factorBlockValue).prod) = 33733573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_2811131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33733573) ^ 16866786 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33733573) ^ 11244524 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33733573) ^ 12 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_34213261 : Nat.Prime 34213261 := by
  apply lucas_primality 34213261 (2 : ZMod 34213261)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (570221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (570221, 1)] : List FactorBlock).map factorBlockValue).prod) = 34213261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_570221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34213261) ^ 17106630 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34213261) ^ 11404420 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34213261) ^ 6842652 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34213261) ^ 60 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_37397897 : Nat.Prime 37397897 := by
  apply lucas_primality 37397897 (3 : ZMod 37397897)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1069, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1069, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) = 37397897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_1069
      · exact prime_fiftyEightBD_4373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 37397897) ^ 18698948 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37397897) ^ 34984 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37397897) ^ 8552 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_38524253 : Nat.Prime 38524253 := by
  apply lucas_primality 38524253 (2 : ZMod 38524253)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (37, 1), (20023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (37, 1), (20023, 1)] : List FactorBlock).map factorBlockValue).prod) = 38524253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_20023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38524253) ^ 19262126 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38524253) ^ 2963404 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38524253) ^ 1041196 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38524253) ^ 1924 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_39949033 : Nat.Prime 39949033 := by
  apply lucas_primality 39949033 (5 : ZMod 39949033)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1664543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1664543, 1)] : List FactorBlock).map factorBlockValue).prod) = 39949033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1664543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 39949033) ^ 19974516 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 39949033) ^ 13316344 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 39949033) ^ 24 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_40277119 : Nat.Prime 40277119 := by
  apply lucas_primality 40277119 (3 : ZMod 40277119)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) = 40277119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_19571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40277119) ^ 20138559 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40277119) ^ 13425706 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40277119) ^ 5753874 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40277119) ^ 2058 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_40776713 : Nat.Prime 40776713 := by
  apply lucas_primality 40776713 (3 : ZMod 40776713)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5097089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5097089, 1)] : List FactorBlock).map factorBlockValue).prod) = 40776713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5097089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 40776713) ^ 20388356 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40776713) ^ 8 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_42138401 : Nat.Prime 42138401 := by
  apply lucas_primality 42138401 (3 : ZMod 42138401)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (52673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (52673, 1)] : List FactorBlock).map factorBlockValue).prod) = 42138401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_52673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42138401) ^ 21069200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42138401) ^ 8427680 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42138401) ^ 800 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_47336617 : Nat.Prime 47336617 := by
  apply lucas_primality 47336617 (5 : ZMod 47336617)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (37, 1), (5923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (37, 1), (5923, 1)] : List FactorBlock).map factorBlockValue).prod) = 47336617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_5923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 47336617) ^ 23668308 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 47336617) ^ 15778872 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 47336617) ^ 1279368 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 47336617) ^ 7992 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_56073341 : Nat.Prime 56073341 := by
  apply lucas_primality 56073341 (3 : ZMod 56073341)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2803667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2803667, 1)] : List FactorBlock).map factorBlockValue).prod) = 56073341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_2803667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56073341) ^ 28036670 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 56073341) ^ 11214668 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 56073341) ^ 20 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_57022331 : Nat.Prime 57022331 := by
  apply lucas_primality 57022331 (2 : ZMod 57022331)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (183943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (183943, 1)] : List FactorBlock).map factorBlockValue).prod) = 57022331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_183943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57022331) ^ 28511165 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57022331) ^ 11404466 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57022331) ^ 1839430 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57022331) ^ 310 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_59997533 : Nat.Prime 59997533 := by
  apply lucas_primality 59997533 (2 : ZMod 59997533)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (73, 1), (149, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (73, 1), (149, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 59997533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_73
      · exact prime_fiftyEightBD_149
      · exact prime_fiftyEightBD_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59997533) ^ 29998766 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59997533) ^ 8571076 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59997533) ^ 821884 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59997533) ^ 402668 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59997533) ^ 304556 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_64557187 : Nat.Prime 64557187 := by
  apply lucas_primality 64557187 (3 : ZMod 64557187)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (110923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (110923, 1)] : List FactorBlock).map factorBlockValue).prod) = 64557187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_97
      · exact prime_fiftyEightBD_110923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64557187) ^ 32278593 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64557187) ^ 21519062 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64557187) ^ 665538 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64557187) ^ 582 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_64784641 : Nat.Prime 64784641 := by
  apply lucas_primality 64784641 (7 : ZMod 64784641)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (16871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (16871, 1)] : List FactorBlock).map factorBlockValue).prod) = 64784641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_16871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 64784641) ^ 32392320 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 64784641) ^ 21594880 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 64784641) ^ 12956928 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 64784641) ^ 3840 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_66459829 : Nat.Prime 66459829 := by
  apply lucas_primality 66459829 (6 : ZMod 66459829)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (811, 1), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (811, 1), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) = 66459829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_811
      · exact prime_fiftyEightBD_6829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 66459829) ^ 33229914 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 66459829) ^ 22153276 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 66459829) ^ 81948 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 66459829) ^ 9732 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_68458333 : Nat.Prime 68458333 := by
  apply lucas_primality 68458333 (2 : ZMod 68458333)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (103, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (103, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 68458333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_97
      · exact prime_fiftyEightBD_103
      · exact prime_fiftyEightBD_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68458333) ^ 34229166 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68458333) ^ 22819444 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68458333) ^ 705756 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68458333) ^ 664644 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68458333) ^ 119892 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_69592751 : Nat.Prime 69592751 := by
  apply lucas_primality 69592751 (7 : ZMod 69592751)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (29, 2), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (29, 2), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 69592751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 69592751) ^ 34796375 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 69592751) ^ 13918550 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 69592751) ^ 2399750 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 69592751) ^ 210250 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_75689051 : Nat.Prime 75689051 := by
  apply lucas_primality 75689051 (6 : ZMod 75689051)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (37, 1), (163, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (37, 1), (163, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 75689051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_163
      · exact prime_fiftyEightBD_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 75689051) ^ 37844525 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 75689051) ^ 15137810 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 75689051) ^ 2045650 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 75689051) ^ 464350 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 75689051) ^ 301550 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_79031791 : Nat.Prime 79031791 := by
  apply lucas_primality 79031791 (3 : ZMod 79031791)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (878131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (878131, 1)] : List FactorBlock).map factorBlockValue).prod) = 79031791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_878131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 79031791) ^ 39515895 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 79031791) ^ 26343930 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 79031791) ^ 15806358 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 79031791) ^ 90 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_79497437 : Nat.Prime 79497437 := by
  apply lucas_primality 79497437 (2 : ZMod 79497437)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (142981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (142981, 1)] : List FactorBlock).map factorBlockValue).prod) = 79497437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_139
      · exact prime_fiftyEightBD_142981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79497437) ^ 39748718 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 79497437) ^ 571924 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 79497437) ^ 556 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_84769031 : Nat.Prime 84769031 := by
  apply lucas_primality 84769031 (7 : ZMod 84769031)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (29, 1), (71, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (29, 1), (71, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 84769031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84769031) ^ 42384515 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 84769031) ^ 16953806 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 84769031) ^ 3685610 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 84769031) ^ 2923070 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 84769031) ^ 1193930 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 84769031) ^ 473570 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_107221291 : Nat.Prime 107221291 := by
  apply lucas_primality 107221291 (2 : ZMod 107221291)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 107221291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_59
      · exact prime_fiftyEightBD_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 107221291) ^ 53610645 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107221291) ^ 35740430 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107221291) ^ 21444258 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107221291) ^ 9747390 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107221291) ^ 1817310 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107221291) ^ 19470 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_109929467 : Nat.Prime 109929467 := by
  apply lucas_primality 109929467 (2 : ZMod 109929467)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (251, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (251, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod) = 109929467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_251
      · exact prime_fiftyEightBD_9521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109929467) ^ 54964733 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 109929467) ^ 4779542 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 109929467) ^ 437966 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 109929467) ^ 11546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_126366971 : Nat.Prime 126366971 := by
  apply lucas_primality 126366971 (2 : ZMod 126366971)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (115933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (115933, 1)] : List FactorBlock).map factorBlockValue).prod) = 126366971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_109
      · exact prime_fiftyEightBD_115933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126366971) ^ 63183485 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 126366971) ^ 25273394 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 126366971) ^ 1159330 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 126366971) ^ 1090 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_149280253 : Nat.Prime 149280253 := by
  apply lucas_primality 149280253 (2 : ZMod 149280253)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (31, 1), (191, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (31, 1), (191, 2)] : List FactorBlock).map factorBlockValue).prod) = 149280253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 149280253) ^ 74640126 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149280253) ^ 49760084 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149280253) ^ 13570932 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149280253) ^ 4815492 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149280253) ^ 781572 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_150158711 : Nat.Prime 150158711 := by
  apply lucas_primality 150158711 (17 : ZMod 150158711)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (19, 1), (60793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (19, 1), (60793, 1)] : List FactorBlock).map factorBlockValue).prod) = 150158711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_19
      · exact prime_fiftyEightBD_60793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 150158711) ^ 75079355 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 150158711) ^ 30031742 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 150158711) ^ 11550670 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 150158711) ^ 7903090 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 150158711) ^ 2470 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_163336757 : Nat.Prime 163336757 := by
  apply lucas_primality 163336757 (3 : ZMod 163336757)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3712199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3712199, 1)] : List FactorBlock).map factorBlockValue).prod) = 163336757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_3712199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 163336757) ^ 81668378 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 163336757) ^ 14848796 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 163336757) ^ 44 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_163931353 : Nat.Prime 163931353 := by
  apply lucas_primality 163931353 (5 : ZMod 163931353)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 3), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 3), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 163931353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 163931353) ^ 81965676 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 163931353) ^ 54643784 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 163931353) ^ 12610104 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 163931353) ^ 52728 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_169538063 : Nat.Prime 169538063 := by
  apply lucas_primality 169538063 (5 : ZMod 169538063)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (84769031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (84769031, 1)] : List FactorBlock).map factorBlockValue).prod) = 169538063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_84769031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 169538063) ^ 84769031 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 169538063) ^ 2 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_194196019 : Nat.Prime 194196019 := by
  apply lucas_primality 194196019 (2 : ZMod 194196019)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32366003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32366003, 1)] : List FactorBlock).map factorBlockValue).prod) = 194196019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_32366003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 194196019) ^ 97098009 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194196019) ^ 64732006 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194196019) ^ 6 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_194783629 : Nat.Prime 194783629 := by
  apply lucas_primality 194783629 (2 : ZMod 194783629)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (491, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (491, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 194783629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_491
      · exact prime_fiftyEightBD_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 194783629) ^ 97391814 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194783629) ^ 64927876 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194783629) ^ 14983356 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194783629) ^ 396708 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194783629) ^ 76596 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_206738957 : Nat.Prime 206738957 := by
  apply lucas_primality 206738957 (2 : ZMod 206738957)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4567, 1), (11317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4567, 1), (11317, 1)] : List FactorBlock).map factorBlockValue).prod) = 206738957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_4567
      · exact prime_fiftyEightBD_11317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 206738957) ^ 103369478 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 206738957) ^ 45268 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 206738957) ^ 18268 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_215119871 : Nat.Prime 215119871 := by
  apply lucas_primality 215119871 (7 : ZMod 215119871)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (180773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (180773, 1)] : List FactorBlock).map factorBlockValue).prod) = 215119871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_180773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 215119871) ^ 107559935 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 215119871) ^ 43023974 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 215119871) ^ 30731410 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 215119871) ^ 12654110 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 215119871) ^ 1190 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_262160771 : Nat.Prime 262160771 := by
  apply lucas_primality 262160771 (2 : ZMod 262160771)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (953, 1), (27509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (953, 1), (27509, 1)] : List FactorBlock).map factorBlockValue).prod) = 262160771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_953
      · exact prime_fiftyEightBD_27509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 262160771) ^ 131080385 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 262160771) ^ 52432154 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 262160771) ^ 275090 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 262160771) ^ 9530 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_270183943 : Nat.Prime 270183943 := by
  apply lucas_primality 270183943 (3 : ZMod 270183943)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (306331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (306331, 1)] : List FactorBlock).map factorBlockValue).prod) = 270183943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_306331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 270183943) ^ 135091971 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 270183943) ^ 90061314 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 270183943) ^ 38597706 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 270183943) ^ 882 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_315529223 : Nat.Prime 315529223 := by
  apply lucas_primality 315529223 (5 : ZMod 315529223)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (31, 1), (113, 1), (1553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (31, 1), (113, 1), (1553, 1)] : List FactorBlock).map factorBlockValue).prod) = 315529223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_113
      · exact prime_fiftyEightBD_1553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 315529223) ^ 157764611 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 315529223) ^ 10880318 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 315529223) ^ 10178362 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 315529223) ^ 2792294 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 315529223) ^ 203174 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_335809237 : Nat.Prime 335809237 := by
  apply lucas_primality 335809237 (5 : ZMod 335809237)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (31, 1), (128959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (31, 1), (128959, 1)] : List FactorBlock).map factorBlockValue).prod) = 335809237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_128959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 335809237) ^ 167904618 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 335809237) ^ 111936412 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 335809237) ^ 47972748 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 335809237) ^ 10832556 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 335809237) ^ 2604 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_358570741 : Nat.Prime 358570741 := by
  apply lucas_primality 358570741 (6 : ZMod 358570741)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (543289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (543289, 1)] : List FactorBlock).map factorBlockValue).prod) = 358570741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_543289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 358570741) ^ 179285370 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 358570741) ^ 119523580 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 358570741) ^ 71714148 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 358570741) ^ 32597340 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 358570741) ^ 660 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_370175543 : Nat.Prime 370175543 := by
  apply lucas_primality 370175543 (5 : ZMod 370175543)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (157, 1), (9743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (157, 1), (9743, 1)] : List FactorBlock).map factorBlockValue).prod) = 370175543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_157
      · exact prime_fiftyEightBD_9743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 370175543) ^ 185087771 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 370175543) ^ 33652322 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 370175543) ^ 2357806 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 370175543) ^ 37994 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_412394189 : Nat.Prime 412394189 := by
  apply lucas_primality 412394189 (2 : ZMod 412394189)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (1747433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (1747433, 1)] : List FactorBlock).map factorBlockValue).prod) = 412394189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_59
      · exact prime_fiftyEightBD_1747433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 412394189) ^ 206197094 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412394189) ^ 6989732 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412394189) ^ 236 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_493191421 : Nat.Prime 493191421 := by
  apply lucas_primality 493191421 (2 : ZMod 493191421)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (131, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (131, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) = 493191421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_131
      · exact prime_fiftyEightBD_3691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 493191421) ^ 246595710 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 493191421) ^ 164397140 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 493191421) ^ 98638284 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 493191421) ^ 29011260 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 493191421) ^ 3764820 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 493191421) ^ 133620 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_541909301 : Nat.Prime 541909301 := by
  apply lucas_primality 541909301 (3 : ZMod 541909301)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (41, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (41, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) = 541909301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_41
      · exact prime_fiftyEightBD_132173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 541909301) ^ 270954650 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 541909301) ^ 108381860 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 541909301) ^ 13217300 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 541909301) ^ 4100 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_563356751 : Nat.Prime 563356751 := by
  apply lucas_primality 563356751 (11 : ZMod 563356751)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (204857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (204857, 1)] : List FactorBlock).map factorBlockValue).prod) = 563356751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_204857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 563356751) ^ 281678375 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 563356751) ^ 112671350 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 563356751) ^ 51214250 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 563356751) ^ 2750 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_570873983 : Nat.Prime 570873983 := by
  apply lucas_primality 570873983 (11 : ZMod 570873983)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (40776713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (40776713, 1)] : List FactorBlock).map factorBlockValue).prod) = 570873983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_40776713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 570873983) ^ 285436991 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 570873983) ^ 81553426 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 570873983) ^ 14 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_572632397 : Nat.Prime 572632397 := by
  apply lucas_primality 572632397 (2 : ZMod 572632397)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (47, 1), (435131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (47, 1), (435131, 1)] : List FactorBlock).map factorBlockValue).prod) = 572632397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_47
      · exact prime_fiftyEightBD_435131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 572632397) ^ 286316198 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 572632397) ^ 81804628 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 572632397) ^ 12183668 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 572632397) ^ 1316 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_661277927 : Nat.Prime 661277927 := by
  apply lucas_primality 661277927 (5 : ZMod 661277927)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (53, 2), (3797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (53, 2), (3797, 1)] : List FactorBlock).map factorBlockValue).prod) = 661277927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_53
      · exact prime_fiftyEightBD_3797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 661277927) ^ 330638963 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 661277927) ^ 21331546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 661277927) ^ 12476942 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 661277927) ^ 174158 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_676420753 : Nat.Prime 676420753 := by
  apply lucas_primality 676420753 (10 : ZMod 676420753)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (17, 1), (79, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (17, 1), (79, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 676420753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_79
      · exact prime_fiftyEightBD_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 676420753) ^ 338210376 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 676420753) ^ 225473584 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 676420753) ^ 96631536 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 676420753) ^ 39789456 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 676420753) ^ 8562288 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 676420753) ^ 451248 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_701948803 : Nat.Prime 701948803 := by
  apply lucas_primality 701948803 (12 : ZMod 701948803)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6881851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6881851, 1)] : List FactorBlock).map factorBlockValue).prod) = 701948803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_6881851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 701948803) ^ 350974401 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (12 : ZMod 701948803) ^ 233982934 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (12 : ZMod 701948803) ^ 41291106 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (12 : ZMod 701948803) ^ 102 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_748828261 : Nat.Prime 748828261 := by
  apply lucas_primality 748828261 (6 : ZMod 748828261)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (307, 1), (4517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (307, 1), (4517, 1)] : List FactorBlock).map factorBlockValue).prod) = 748828261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_307
      · exact prime_fiftyEightBD_4517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 748828261) ^ 374414130 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 748828261) ^ 249609420 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 748828261) ^ 149765652 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 748828261) ^ 2439180 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 748828261) ^ 165780 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_790632517 : Nat.Prime 790632517 := by
  apply lucas_primality 790632517 (5 : ZMod 790632517)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1583, 1), (41621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1583, 1), (41621, 1)] : List FactorBlock).map factorBlockValue).prod) = 790632517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1583
      · exact prime_fiftyEightBD_41621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 790632517) ^ 395316258 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 790632517) ^ 263544172 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 790632517) ^ 499452 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 790632517) ^ 18996 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_884963749 : Nat.Prime 884963749 := by
  apply lucas_primality 884963749 (2 : ZMod 884963749)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1993, 1), (37003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1993, 1), (37003, 1)] : List FactorBlock).map factorBlockValue).prod) = 884963749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1993
      · exact prime_fiftyEightBD_37003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 884963749) ^ 442481874 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 884963749) ^ 294987916 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 884963749) ^ 444036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 884963749) ^ 23916 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1067994637 : Nat.Prime 1067994637 := by
  apply lucas_primality 1067994637 (2 : ZMod 1067994637)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (59, 1), (79393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (59, 1), (79393, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067994637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_19
      · exact prime_fiftyEightBD_59
      · exact prime_fiftyEightBD_79393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1067994637) ^ 533997318 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067994637) ^ 355998212 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067994637) ^ 56210244 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067994637) ^ 18101604 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067994637) ^ 13452 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1079950873 : Nat.Prime 1079950873 := by
  apply lucas_primality 1079950873 (5 : ZMod 1079950873)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (13, 1), (44953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (13, 1), (44953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079950873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_44953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1079950873) ^ 539975436 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079950873) ^ 359983624 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079950873) ^ 154278696 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079950873) ^ 98177352 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079950873) ^ 83073144 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079950873) ^ 24024 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1136078809 : Nat.Prime 1136078809 := by
  apply lucas_primality 1136078809 (13 : ZMod 1136078809)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47336617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47336617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1136078809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_47336617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1136078809) ^ 568039404 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1136078809) ^ 378692936 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1136078809) ^ 24 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1223294929 : Nat.Prime 1223294929 := by
  apply lucas_primality 1223294929 (11 : ZMod 1223294929)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (1108057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (1108057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1223294929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_1108057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1223294929) ^ 611647464 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1223294929) ^ 407764976 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1223294929) ^ 53186736 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1223294929) ^ 1104 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1264508657 : Nat.Prime 1264508657 := by
  apply lucas_primality 1264508657 (3 : ZMod 1264508657)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (79031791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (79031791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264508657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_79031791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1264508657) ^ 632254328 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264508657) ^ 16 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1311859957 : Nat.Prime 1311859957 := by
  apply lucas_primality 1311859957 (5 : ZMod 1311859957)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (683, 1), (14551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (683, 1), (14551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1311859957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_683
      · exact prime_fiftyEightBD_14551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1311859957) ^ 655929978 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1311859957) ^ 437286652 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1311859957) ^ 119259996 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1311859957) ^ 1920732 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1311859957) ^ 90156 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1568319637 : Nat.Prime 1568319637 := by
  apply lucas_primality 1568319637 (5 : ZMod 1568319637)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (324301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (324301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1568319637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_324301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1568319637) ^ 784159818 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1568319637) ^ 522773212 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1568319637) ^ 120639972 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1568319637) ^ 50590956 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1568319637) ^ 4836 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2403426307 : Nat.Prime 2403426307 := by
  apply lucas_primality 2403426307 (5 : ZMod 2403426307)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (211, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (211, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) = 2403426307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_211
      · exact prime_fiftyEightBD_6569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2403426307) ^ 1201713153 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403426307) ^ 801142102 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403426307) ^ 141378018 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403426307) ^ 11390646 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403426307) ^ 365874 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2533200701 : Nat.Prime 2533200701 := by
  apply lucas_primality 2533200701 (2 : ZMod 2533200701)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (25332007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (25332007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2533200701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_25332007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2533200701) ^ 1266600350 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2533200701) ^ 506640140 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2533200701) ^ 100 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2762484971 : Nat.Prime 2762484971 := by
  apply lucas_primality 2762484971 (2 : ZMod 2762484971)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (811, 1), (48661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (811, 1), (48661, 1)] : List FactorBlock).map factorBlockValue).prod) = 2762484971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_811
      · exact prime_fiftyEightBD_48661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2762484971) ^ 1381242485 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2762484971) ^ 552496994 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2762484971) ^ 394640710 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2762484971) ^ 3406270 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2762484971) ^ 56770 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3062756899 : Nat.Prime 3062756899 := by
  apply lucas_primality 3062756899 (2 : ZMod 3062756899)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (757, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (757, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 3062756899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_53
      · exact prime_fiftyEightBD_757
      · exact prime_fiftyEightBD_4241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3062756899) ^ 1531378449 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3062756899) ^ 1020918966 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3062756899) ^ 57787866 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3062756899) ^ 4045914 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3062756899) ^ 722178 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3146468257 : Nat.Prime 3146468257 := by
  apply lucas_primality 3146468257 (5 : ZMod 3146468257)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (17, 1), (31, 1), (20731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (17, 1), (31, 1), (20731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3146468257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_20731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3146468257) ^ 1573234128 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146468257) ^ 1048822752 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146468257) ^ 185086368 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146468257) ^ 101498976 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146468257) ^ 151776 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3282213419 : Nat.Prime 3282213419 := by
  apply lucas_primality 3282213419 (2 : ZMod 3282213419)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (71, 1), (499, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (71, 1), (499, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 3282213419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_499
      · exact prime_fiftyEightBD_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3282213419) ^ 1641106709 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282213419) ^ 298383038 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282213419) ^ 46228358 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282213419) ^ 6577582 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282213419) ^ 779438 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3317595317 : Nat.Prime 3317595317 := by
  apply lucas_primality 3317595317 (3 : ZMod 3317595317)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (1768441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (1768441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3317595317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_67
      · exact prime_fiftyEightBD_1768441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3317595317) ^ 1658797658 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3317595317) ^ 473942188 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3317595317) ^ 49516348 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3317595317) ^ 1876 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3967667563 : Nat.Prime 3967667563 := by
  apply lucas_primality 3967667563 (2 : ZMod 3967667563)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (661277927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (661277927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3967667563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_661277927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3967667563) ^ 1983833781 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3967667563) ^ 1322555854 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3967667563) ^ 6 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4585641199 : Nat.Prime 4585641199 := by
  apply lucas_primality 4585641199 (15 : ZMod 4585641199)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (16261139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (16261139, 1)] : List FactorBlock).map factorBlockValue).prod) = 4585641199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_47
      · exact prime_fiftyEightBD_16261139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 4585641199) ^ 2292820599 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (15 : ZMod 4585641199) ^ 1528547066 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (15 : ZMod 4585641199) ^ 97566834 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (15 : ZMod 4585641199) ^ 282 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4710915431 : Nat.Prime 4710915431 := by
  apply lucas_primality 4710915431 (17 : ZMod 4710915431)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (1575557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (1575557, 1)] : List FactorBlock).map factorBlockValue).prod) = 4710915431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_1575557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4710915431) ^ 2355457715 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 4710915431) ^ 942183086 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 4710915431) ^ 362378110 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 4710915431) ^ 204822410 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (17 : ZMod 4710915431) ^ 2990 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5039709361 : Nat.Prime 5039709361 := by
  apply lucas_primality 5039709361 (13 : ZMod 5039709361)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (2999827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (2999827, 1)] : List FactorBlock).map factorBlockValue).prod) = 5039709361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_2999827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5039709361) ^ 2519854680 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 5039709361) ^ 1679903120 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 5039709361) ^ 1007941872 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 5039709361) ^ 719958480 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 5039709361) ^ 1680 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5944046747 : Nat.Prime 5944046747 := by
  apply lucas_primality 5944046747 (5 : ZMod 5944046747)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (270183943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (270183943, 1)] : List FactorBlock).map factorBlockValue).prod) = 5944046747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_270183943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5944046747) ^ 2972023373 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5944046747) ^ 540367886 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5944046747) ^ 22 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_6670316813 : Nat.Prime 6670316813 := by
  apply lucas_primality 6670316813 (2 : ZMod 6670316813)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25741, 1), (64783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25741, 1), (64783, 1)] : List FactorBlock).map factorBlockValue).prod) = 6670316813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_25741
      · exact prime_fiftyEightBD_64783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6670316813) ^ 3335158406 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6670316813) ^ 259132 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6670316813) ^ 102964 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_6996105827 : Nat.Prime 6996105827 := by
  apply lucas_primality 6996105827 (2 : ZMod 6996105827)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (12360611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (12360611, 1)] : List FactorBlock).map factorBlockValue).prod) = 6996105827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_283
      · exact prime_fiftyEightBD_12360611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6996105827) ^ 3498052913 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6996105827) ^ 24721222 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6996105827) ^ 566 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_7587051943 : Nat.Prime 7587051943 := by
  apply lucas_primality 7587051943 (5 : ZMod 7587051943)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1264508657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1264508657, 1)] : List FactorBlock).map factorBlockValue).prod) = 7587051943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1264508657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7587051943) ^ 3793525971 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7587051943) ^ 2529017314 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7587051943) ^ 6 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_8364046973 : Nat.Prime 8364046973 := by
  apply lucas_primality 8364046973 (3 : ZMod 8364046973)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (503, 1), (70459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (503, 1), (70459, 1)] : List FactorBlock).map factorBlockValue).prod) = 8364046973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_59
      · exact prime_fiftyEightBD_503
      · exact prime_fiftyEightBD_70459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8364046973) ^ 4182023486 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8364046973) ^ 141763508 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8364046973) ^ 16628324 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8364046973) ^ 118708 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_8392456213 : Nat.Prime 8392456213 := by
  apply lucas_primality 8392456213 (13 : ZMod 8392456213)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (113, 1), (617, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (113, 1), (617, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) = 8392456213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_113
      · exact prime_fiftyEightBD_617
      · exact prime_fiftyEightBD_1433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8392456213) ^ 4196228106 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8392456213) ^ 2797485404 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8392456213) ^ 1198922316 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8392456213) ^ 74269524 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8392456213) ^ 13602036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8392456213) ^ 5856564 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_8485445789 : Nat.Prime 8485445789 := by
  apply lucas_primality 8485445789 (2 : ZMod 8485445789)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25633, 1), (82759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25633, 1), (82759, 1)] : List FactorBlock).map factorBlockValue).prod) = 8485445789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_25633
      · exact prime_fiftyEightBD_82759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8485445789) ^ 4242722894 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8485445789) ^ 331036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8485445789) ^ 102532 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_9788036227 : Nat.Prime 9788036227 := by
  apply lucas_primality 9788036227 (5 : ZMod 9788036227)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (10008217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (10008217, 1)] : List FactorBlock).map factorBlockValue).prod) = 9788036227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_163
      · exact prime_fiftyEightBD_10008217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9788036227) ^ 4894018113 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9788036227) ^ 3262678742 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9788036227) ^ 60049302 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9788036227) ^ 978 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_10518315967 : Nat.Prime 10518315967 := by
  apply lucas_primality 10518315967 (5 : ZMod 10518315967)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (194783629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (194783629, 1)] : List FactorBlock).map factorBlockValue).prod) = 10518315967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_194783629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10518315967) ^ 5259157983 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10518315967) ^ 3506105322 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10518315967) ^ 54 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_10898412403 : Nat.Prime 10898412403 := by
  apply lucas_primality 10898412403 (2 : ZMod 10898412403)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6581, 1), (276007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6581, 1), (276007, 1)] : List FactorBlock).map factorBlockValue).prod) = 10898412403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_6581
      · exact prime_fiftyEightBD_276007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10898412403) ^ 5449206201 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10898412403) ^ 3632804134 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10898412403) ^ 1656042 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10898412403) ^ 39486 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_11254030063 : Nat.Prime 11254030063 := by
  apply lucas_primality 11254030063 (11 : ZMod 11254030063)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1361, 1), (125287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1361, 1), (125287, 1)] : List FactorBlock).map factorBlockValue).prod) = 11254030063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_1361
      · exact prime_fiftyEightBD_125287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11254030063) ^ 5627015031 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11254030063) ^ 3751343354 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11254030063) ^ 1023093642 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11254030063) ^ 8268942 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11254030063) ^ 89826 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_15196245401 : Nat.Prime 15196245401 := by
  apply lucas_primality 15196245401 (3 : ZMod 15196245401)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (10854461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (10854461, 1)] : List FactorBlock).map factorBlockValue).prod) = 15196245401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_10854461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15196245401) ^ 7598122700 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15196245401) ^ 3039249080 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15196245401) ^ 2170892200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15196245401) ^ 1400 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_16031129131 : Nat.Prime 16031129131 := by
  apply lucas_primality 16031129131 (2 : ZMod 16031129131)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (197, 1), (904181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (197, 1), (904181, 1)] : List FactorBlock).map factorBlockValue).prod) = 16031129131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_197
      · exact prime_fiftyEightBD_904181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16031129131) ^ 8015564565 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16031129131) ^ 5343709710 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16031129131) ^ 3206225826 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16031129131) ^ 81376290 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16031129131) ^ 17730 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_16291854143 : Nat.Prime 16291854143 := by
  apply lucas_primality 16291854143 (5 : ZMod 16291854143)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (8476511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (8476511, 1)] : List FactorBlock).map factorBlockValue).prod) = 16291854143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_8476511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16291854143) ^ 8145927071 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16291854143) ^ 525543682 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16291854143) ^ 1922 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_18823066411 : Nat.Prime 18823066411 := by
  apply lucas_primality 18823066411 (2 : ZMod 18823066411)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (241, 1), (2603467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (241, 1), (2603467, 1)] : List FactorBlock).map factorBlockValue).prod) = 18823066411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_241
      · exact prime_fiftyEightBD_2603467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18823066411) ^ 9411533205 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18823066411) ^ 6274355470 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18823066411) ^ 3764613282 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18823066411) ^ 78104010 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18823066411) ^ 7230 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_19049070493 : Nat.Prime 19049070493 := by
  apply lucas_primality 19049070493 (2 : ZMod 19049070493)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (15439, 1), (34273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (15439, 1), (34273, 1)] : List FactorBlock).map factorBlockValue).prod) = 19049070493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_15439
      · exact prime_fiftyEightBD_34273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19049070493) ^ 9524535246 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19049070493) ^ 6349690164 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19049070493) ^ 1233828 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19049070493) ^ 555804 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_20065160287 : Nat.Prime 20065160287 := by
  apply lucas_primality 20065160287 (3 : ZMod 20065160287)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4597, 1), (242491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4597, 1), (242491, 1)] : List FactorBlock).map factorBlockValue).prod) = 20065160287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_4597
      · exact prime_fiftyEightBD_242491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20065160287) ^ 10032580143 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20065160287) ^ 6688386762 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20065160287) ^ 4364838 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20065160287) ^ 82746 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_23664871499 : Nat.Prime 23664871499 := by
  apply lucas_primality 23664871499 (2 : ZMod 23664871499)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25247, 1), (468667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25247, 1), (468667, 1)] : List FactorBlock).map factorBlockValue).prod) = 23664871499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_25247
      · exact prime_fiftyEightBD_468667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23664871499) ^ 11832435749 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23664871499) ^ 937334 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23664871499) ^ 50494 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_28856898229 : Nat.Prime 28856898229 := by
  apply lucas_primality 28856898229 (6 : ZMod 28856898229)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (8557799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (8557799, 1)] : List FactorBlock).map factorBlockValue).prod) = 28856898229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_281
      · exact prime_fiftyEightBD_8557799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 28856898229) ^ 14428449114 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 28856898229) ^ 9618966076 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 28856898229) ^ 102693588 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 28856898229) ^ 3372 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_30392490803 : Nat.Prime 30392490803 := by
  apply lucas_primality 30392490803 (2 : ZMod 30392490803)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15196245401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15196245401, 1)] : List FactorBlock).map factorBlockValue).prod) = 30392490803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_15196245401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30392490803) ^ 15196245401 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 30392490803) ^ 2 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_33271506817 : Nat.Prime 33271506817 := by
  apply lucas_primality 33271506817 (5 : ZMod 33271506817)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5449, 1), (15901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5449, 1), (15901, 1)] : List FactorBlock).map factorBlockValue).prod) = 33271506817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5449
      · exact prime_fiftyEightBD_15901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33271506817) ^ 16635753408 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33271506817) ^ 11090502272 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33271506817) ^ 6105984 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33271506817) ^ 2092416 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_36369095783 : Nat.Prime 36369095783 := by
  apply lucas_primality 36369095783 (5 : ZMod 36369095783)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (790632517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (790632517, 1)] : List FactorBlock).map factorBlockValue).prod) = 36369095783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_790632517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 36369095783) ^ 18184547891 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36369095783) ^ 1581265034 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36369095783) ^ 46 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_39003162839 : Nat.Prime 39003162839 := by
  apply lucas_primality 39003162839 (7 : ZMod 39003162839)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (109, 1), (937, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (109, 1), (937, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) = 39003162839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_79
      · exact prime_fiftyEightBD_109
      · exact prime_fiftyEightBD_937
      · exact prime_fiftyEightBD_2417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39003162839) ^ 19501581419 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39003162839) ^ 493710922 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39003162839) ^ 357827182 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39003162839) ^ 41625574 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39003162839) ^ 16137014 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_39185845091 : Nat.Prime 39185845091 := by
  apply lucas_primality 39185845091 (2 : ZMod 39185845091)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (157, 1), (3565591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (157, 1), (3565591, 1)] : List FactorBlock).map factorBlockValue).prod) = 39185845091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_157
      · exact prime_fiftyEightBD_3565591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39185845091) ^ 19592922545 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39185845091) ^ 7837169018 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39185845091) ^ 5597977870 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39185845091) ^ 249591370 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39185845091) ^ 10990 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_42170333129 : Nat.Prime 42170333129 := by
  apply lucas_primality 42170333129 (3 : ZMod 42170333129)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (68458333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (68458333, 1)] : List FactorBlock).map factorBlockValue).prod) = 42170333129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_68458333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42170333129) ^ 21085166564 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42170333129) ^ 6024333304 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42170333129) ^ 3833666648 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42170333129) ^ 616 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_49117671373 : Nat.Prime 49117671373 := by
  apply lucas_primality 49117671373 (14 : ZMod 49117671373)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (31, 1), (89, 1), (19267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (31, 1), (89, 1), (19267, 1)] : List FactorBlock).map factorBlockValue).prod) = 49117671373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_89
      · exact prime_fiftyEightBD_19267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 49117671373) ^ 24558835686 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (14 : ZMod 49117671373) ^ 16372557124 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (14 : ZMod 49117671373) ^ 7016810196 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (14 : ZMod 49117671373) ^ 4465242852 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (14 : ZMod 49117671373) ^ 1584441012 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (14 : ZMod 49117671373) ^ 551883948 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (14 : ZMod 49117671373) ^ 2549316 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_57109851613 : Nat.Prime 57109851613 := by
  apply lucas_primality 57109851613 (2 : ZMod 57109851613)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (17, 1), (29, 1), (43, 1), (6803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (17, 1), (29, 1), (43, 1), (6803, 1)] : List FactorBlock).map factorBlockValue).prod) = 57109851613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_43
      · exact prime_fiftyEightBD_6803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57109851613) ^ 28554925806 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57109851613) ^ 19036617204 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57109851613) ^ 5191804692 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57109851613) ^ 3359403036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57109851613) ^ 1969305228 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57109851613) ^ 1328136084 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57109851613) ^ 8394804 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_80009037529 : Nat.Prime 80009037529 := by
  apply lucas_primality 80009037529 (13 : ZMod 80009037529)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (157, 1), (3033403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (157, 1), (3033403, 1)] : List FactorBlock).map factorBlockValue).prod) = 80009037529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_157
      · exact prime_fiftyEightBD_3033403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 80009037529) ^ 40004518764 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 80009037529) ^ 26669679176 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 80009037529) ^ 11429862504 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 80009037529) ^ 509611704 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 80009037529) ^ 26376 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_80043801757 : Nat.Prime 80043801757 := by
  apply lucas_primality 80043801757 (2 : ZMod 80043801757)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6670316813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6670316813, 1)] : List FactorBlock).map factorBlockValue).prod) = 80043801757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_6670316813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 80043801757) ^ 40021900878 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80043801757) ^ 26681267252 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80043801757) ^ 12 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_90134985203 : Nat.Prime 90134985203 := by
  apply lucas_primality 90134985203 (2 : ZMod 90134985203)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (157, 1), (677, 1), (14621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (157, 1), (677, 1), (14621, 1)] : List FactorBlock).map factorBlockValue).prod) = 90134985203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_157
      · exact prime_fiftyEightBD_677
      · exact prime_fiftyEightBD_14621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90134985203) ^ 45067492601 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90134985203) ^ 3108102938 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90134985203) ^ 574108186 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90134985203) ^ 133138826 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90134985203) ^ 6164762 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_95465037209 : Nat.Prime 95465037209 := by
  apply lucas_primality 95465037209 (6 : ZMod 95465037209)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (701948803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (701948803, 1)] : List FactorBlock).map factorBlockValue).prod) = 95465037209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_701948803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 95465037209) ^ 47732518604 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 95465037209) ^ 5615590424 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 95465037209) ^ 136 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_110637803327 : Nat.Prime 110637803327 := by
  apply lucas_primality 110637803327 (5 : ZMod 110637803327)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (7013, 1), (464003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (7013, 1), (464003, 1)] : List FactorBlock).map factorBlockValue).prod) = 110637803327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_7013
      · exact prime_fiftyEightBD_464003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 110637803327) ^ 55318901663 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 110637803327) ^ 6508106078 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 110637803327) ^ 15776102 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 110637803327) ^ 238442 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_151114156651 : Nat.Prime 151114156651 := by
  apply lucas_primality 151114156651 (12 : ZMod 151114156651)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (335809237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (335809237, 1)] : List FactorBlock).map factorBlockValue).prod) = 151114156651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_335809237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 151114156651) ^ 75557078325 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (12 : ZMod 151114156651) ^ 50371385550 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (12 : ZMod 151114156651) ^ 30222831330 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (12 : ZMod 151114156651) ^ 450 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_155647840273 : Nat.Prime 155647840273 := by
  apply lucas_primality 155647840273 (5 : ZMod 155647840273)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (83, 1), (831239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (83, 1), (831239, 1)] : List FactorBlock).map factorBlockValue).prod) = 155647840273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_47
      · exact prime_fiftyEightBD_83
      · exact prime_fiftyEightBD_831239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155647840273) ^ 77823920136 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 155647840273) ^ 51882613424 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 155647840273) ^ 3311656176 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 155647840273) ^ 1875275184 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 155647840273) ^ 187248 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_161840710529 : Nat.Prime 161840710529 := by
  apply lucas_primality 161840710529 (6 : ZMod 161840710529)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (461, 1), (467, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (461, 1), (467, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 161840710529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_461
      · exact prime_fiftyEightBD_467
      · exact prime_fiftyEightBD_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 161840710529) ^ 80920355264 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 161840710529) ^ 23120101504 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 161840710529) ^ 351064448 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 161840710529) ^ 346553984 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 161840710529) ^ 192897152 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_189318971993 : Nat.Prime 189318971993 := by
  apply lucas_primality 189318971993 (3 : ZMod 189318971993)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23664871499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23664871499, 1)] : List FactorBlock).map factorBlockValue).prod) = 189318971993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_23664871499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 189318971993) ^ 94659485996 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 189318971993) ^ 8 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_197213907551 : Nat.Prime 197213907551 := by
  apply lucas_primality 197213907551 (13 : ZMod 197213907551)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (358570741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (358570741, 1)] : List FactorBlock).map factorBlockValue).prod) = 197213907551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_358570741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 197213907551) ^ 98606953775 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 197213907551) ^ 39442781510 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 197213907551) ^ 17928537050 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 197213907551) ^ 550 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_316481705699 : Nat.Prime 316481705699 := by
  apply lucas_primality 316481705699 (2 : ZMod 316481705699)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2381, 1), (66459829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2381, 1), (66459829, 1)] : List FactorBlock).map factorBlockValue).prod) = 316481705699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_2381
      · exact prime_fiftyEightBD_66459829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 316481705699) ^ 158240852849 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 316481705699) ^ 132919658 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 316481705699) ^ 4762 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_514192536971 : Nat.Prime 514192536971 := by
  apply lucas_primality 514192536971 (2 : ZMod 514192536971)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (131, 1), (56073341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (131, 1), (56073341, 1)] : List FactorBlock).map factorBlockValue).prod) = 514192536971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_131
      · exact prime_fiftyEightBD_56073341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 514192536971) ^ 257096268485 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 514192536971) ^ 102838507394 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 514192536971) ^ 73456076710 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 514192536971) ^ 3925133870 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 514192536971) ^ 9170 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_551783424883 : Nat.Prime 551783424883 := by
  apply lucas_primality 551783424883 (2 : ZMod 551783424883)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (412394189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (412394189, 1)] : List FactorBlock).map factorBlockValue).prod) = 551783424883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_223
      · exact prime_fiftyEightBD_412394189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 551783424883) ^ 275891712441 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 551783424883) ^ 183927808294 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 551783424883) ^ 2474365134 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 551783424883) ^ 1338 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_614365244879 : Nat.Prime 614365244879 := by
  apply lucas_primality 614365244879 (11 : ZMod 614365244879)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 2), (23, 1), (71, 1), (31727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 2), (23, 1), (71, 1), (31727, 1)] : List FactorBlock).map factorBlockValue).prod) = 614365244879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_31727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 614365244879) ^ 307182622439 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 614365244879) ^ 87766463554 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 614365244879) ^ 55851385898 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 614365244879) ^ 26711532386 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 614365244879) ^ 8653031618 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 614365244879) ^ 19364114 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_685318219357 : Nat.Prime 685318219357 := by
  apply lucas_primality 685318219357 (2 : ZMod 685318219357)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (57109851613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (57109851613, 1)] : List FactorBlock).map factorBlockValue).prod) = 685318219357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_57109851613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 685318219357) ^ 342659109678 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 685318219357) ^ 228439406452 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 685318219357) ^ 12 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_694208853823 : Nat.Prime 694208853823 := by
  apply lucas_primality 694208853823 (3 : ZMod 694208853823)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (10518315967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (10518315967, 1)] : List FactorBlock).map factorBlockValue).prod) = 694208853823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_10518315967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 694208853823) ^ 347104426911 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 694208853823) ^ 231402951274 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 694208853823) ^ 63109895802 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 694208853823) ^ 66 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_707463351319 : Nat.Prime 707463351319 := by
  apply lucas_primality 707463351319 (3 : ZMod 707463351319)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (787, 1), (8813107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (787, 1), (8813107, 1)] : List FactorBlock).map factorBlockValue).prod) = 707463351319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_787
      · exact prime_fiftyEightBD_8813107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 707463351319) ^ 353731675659 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 707463351319) ^ 235821117106 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 707463351319) ^ 41615491254 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 707463351319) ^ 898936914 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 707463351319) ^ 80274 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_776537208959 : Nat.Prime 776537208959 := by
  apply lucas_primality 776537208959 (7 : ZMod 776537208959)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (37, 1), (9311221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (37, 1), (9311221, 1)] : List FactorBlock).map factorBlockValue).prod) = 776537208959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_9311221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 776537208959) ^ 388268604479 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 776537208959) ^ 110933886994 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 776537208959) ^ 33762487346 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 776537208959) ^ 20987492134 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 776537208959) ^ 83398 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1028385073943 : Nat.Prime 1028385073943 := by
  apply lucas_primality 1028385073943 (5 : ZMod 1028385073943)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (514192536971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (514192536971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1028385073943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_514192536971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1028385073943) ^ 514192536971 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1028385073943) ^ 2 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1172684798867 : Nat.Prime 1172684798867 := by
  apply lucas_primality 1172684798867 (2 : ZMod 1172684798867)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13921, 1), (859577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13921, 1), (859577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1172684798867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_13921
      · exact prime_fiftyEightBD_859577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1172684798867) ^ 586342399433 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172684798867) ^ 167526399838 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172684798867) ^ 84238546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172684798867) ^ 1364258 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1184182949927 : Nat.Prime 1184182949927 := by
  apply lucas_primality 1184182949927 (5 : ZMod 1184182949927)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (601, 1), (12470597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (601, 1), (12470597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184182949927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_79
      · exact prime_fiftyEightBD_601
      · exact prime_fiftyEightBD_12470597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1184182949927) ^ 592091474963 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184182949927) ^ 14989657594 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184182949927) ^ 1970354326 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184182949927) ^ 94958 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1394561063723 : Nat.Prime 1394561063723 := by
  apply lucas_primality 1394561063723 (2 : ZMod 1394561063723)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (18443, 1), (240811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (18443, 1), (240811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1394561063723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_157
      · exact prime_fiftyEightBD_18443
      · exact prime_fiftyEightBD_240811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1394561063723) ^ 697280531861 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394561063723) ^ 8882554546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394561063723) ^ 75614654 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394561063723) ^ 5791102 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1541678868883 : Nat.Prime 1541678868883 := by
  apply lucas_primality 1541678868883 (2 : ZMod 1541678868883)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13313, 1), (2144491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13313, 1), (2144491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1541678868883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13313
      · exact prime_fiftyEightBD_2144491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1541678868883) ^ 770839434441 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541678868883) ^ 513892956294 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541678868883) ^ 115802514 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541678868883) ^ 718902 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2125153681709 : Nat.Prime 2125153681709 := by
  apply lucas_primality 2125153681709 (2 : ZMod 2125153681709)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3559, 1), (149280253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3559, 1), (149280253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2125153681709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3559
      · exact prime_fiftyEightBD_149280253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2125153681709) ^ 1062576840854 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2125153681709) ^ 597121012 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2125153681709) ^ 14236 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2167371819661 : Nat.Prime 2167371819661 := by
  apply lucas_primality 2167371819661 (2 : ZMod 2167371819661)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (39359, 1), (53987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (39359, 1), (53987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2167371819661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_39359
      · exact prime_fiftyEightBD_53987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2167371819661) ^ 1083685909830 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167371819661) ^ 722457273220 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167371819661) ^ 433474363932 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167371819661) ^ 127492459980 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167371819661) ^ 55066740 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167371819661) ^ 40146180 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2266667347391 : Nat.Prime 2266667347391 := by
  apply lucas_primality 2266667347391 (13 : ZMod 2266667347391)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9743, 1), (23264573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9743, 1), (23264573, 1)] : List FactorBlock).map factorBlockValue).prod) = 2266667347391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_9743
      · exact prime_fiftyEightBD_23264573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2266667347391) ^ 1133333673695 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 2266667347391) ^ 453333469478 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 2266667347391) ^ 232645730 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 2266667347391) ^ 97430 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2473124050003 : Nat.Prime 2473124050003 := by
  apply lucas_primality 2473124050003 (3 : ZMod 2473124050003)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (3146468257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (3146468257, 1)] : List FactorBlock).map factorBlockValue).prod) = 2473124050003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_131
      · exact prime_fiftyEightBD_3146468257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2473124050003) ^ 1236562025001 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2473124050003) ^ 824374683334 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2473124050003) ^ 18878809542 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2473124050003) ^ 786 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3207019243319 : Nat.Prime 3207019243319 := by
  apply lucas_primality 3207019243319 (11 : ZMod 3207019243319)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (269, 1), (541909301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (269, 1), (541909301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3207019243319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_269
      · exact prime_fiftyEightBD_541909301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3207019243319) ^ 1603509621659 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3207019243319) ^ 291547203938 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3207019243319) ^ 11922004622 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3207019243319) ^ 5918 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3259669256383 : Nat.Prime 3259669256383 := by
  apply lucas_primality 3259669256383 (3 : ZMod 3259669256383)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (67, 1), (2699, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (67, 1), (2699, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) = 3259669256383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_67
      · exact prime_fiftyEightBD_2699
      · exact prime_fiftyEightBD_3547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3259669256383) ^ 1629834628191 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3259669256383) ^ 1086556418794 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3259669256383) ^ 465667036626 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3259669256383) ^ 296333568762 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3259669256383) ^ 48651779946 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3259669256383) ^ 1207732218 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3259669256383) ^ 918993306 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3276853561901 : Nat.Prime 3276853561901 := by
  apply lucas_primality 3276853561901 (2 : ZMod 3276853561901)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (52259, 1), (627041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (52259, 1), (627041, 1)] : List FactorBlock).map factorBlockValue).prod) = 3276853561901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_52259
      · exact prime_fiftyEightBD_627041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3276853561901) ^ 1638426780950 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3276853561901) ^ 655370712380 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3276853561901) ^ 62704100 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3276853561901) ^ 5225900 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4160059057093 : Nat.Prime 4160059057093 := by
  apply lucas_primality 4160059057093 (2 : ZMod 4160059057093)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (167, 1), (10289, 1), (201757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (167, 1), (10289, 1), (201757, 1)] : List FactorBlock).map factorBlockValue).prod) = 4160059057093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_167
      · exact prime_fiftyEightBD_10289
      · exact prime_fiftyEightBD_201757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4160059057093) ^ 2080029528546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160059057093) ^ 1386686352364 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160059057093) ^ 24910533276 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160059057093) ^ 404321028 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160059057093) ^ 20619156 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4468554523717 : Nat.Prime 4468554523717 := by
  apply lucas_primality 4468554523717 (2 : ZMod 4468554523717)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (151, 1), (107221291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (151, 1), (107221291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4468554523717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_151
      · exact prime_fiftyEightBD_107221291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4468554523717) ^ 2234277261858 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4468554523717) ^ 1489518174572 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4468554523717) ^ 194284979292 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4468554523717) ^ 29593076316 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4468554523717) ^ 41676 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4766380291669 : Nat.Prime 4766380291669 := by
  apply lucas_primality 4766380291669 (7 : ZMod 4766380291669)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (37, 1), (370175543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (37, 1), (370175543, 1)] : List FactorBlock).map factorBlockValue).prod) = 4766380291669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_370175543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4766380291669) ^ 2383190145834 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 4766380291669) ^ 1588793430556 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 4766380291669) ^ 164357941092 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 4766380291669) ^ 128821088964 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 4766380291669) ^ 12876 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4855221315871 : Nat.Prime 4855221315871 := by
  apply lucas_primality 4855221315871 (3 : ZMod 4855221315871)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (161840710529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (161840710529, 1)] : List FactorBlock).map factorBlockValue).prod) = 4855221315871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_161840710529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4855221315871) ^ 2427610657935 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4855221315871) ^ 1618407105290 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4855221315871) ^ 971044263174 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4855221315871) ^ 30 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5523666976931 : Nat.Prime 5523666976931 := by
  apply lucas_primality 5523666976931 (2 : ZMod 5523666976931)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79813, 1), (6920761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79813, 1), (6920761, 1)] : List FactorBlock).map factorBlockValue).prod) = 5523666976931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_79813
      · exact prime_fiftyEightBD_6920761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5523666976931) ^ 2761833488465 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5523666976931) ^ 1104733395386 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5523666976931) ^ 69207610 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5523666976931) ^ 798130 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_6050996733671 : Nat.Prime 6050996733671 := by
  apply lucas_primality 6050996733671 (7 : ZMod 6050996733671)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (182111, 1), (474671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (182111, 1), (474671, 1)] : List FactorBlock).map factorBlockValue).prod) = 6050996733671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_182111
      · exact prime_fiftyEightBD_474671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6050996733671) ^ 3025498366835 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6050996733671) ^ 1210199346734 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6050996733671) ^ 864428104810 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6050996733671) ^ 33226970 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6050996733671) ^ 12747770 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_6402803601221 : Nat.Prime 6402803601221 := by
  apply lucas_primality 6402803601221 (2 : ZMod 6402803601221)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (1511, 1), (16297927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (1511, 1), (16297927, 1)] : List FactorBlock).map factorBlockValue).prod) = 6402803601221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_1511
      · exact prime_fiftyEightBD_16297927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6402803601221) ^ 3201401800610 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6402803601221) ^ 1280560720244 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6402803601221) ^ 492523353940 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6402803601221) ^ 4237461020 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6402803601221) ^ 392860 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_9653584412327 : Nat.Prime 9653584412327 := by
  apply lucas_primality 9653584412327 (5 : ZMod 9653584412327)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (2087, 1), (16881677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (2087, 1), (16881677, 1)] : List FactorBlock).map factorBlockValue).prod) = 9653584412327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_137
      · exact prime_fiftyEightBD_2087
      · exact prime_fiftyEightBD_16881677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9653584412327) ^ 4826792206163 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9653584412327) ^ 70464119798 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9653584412327) ^ 4625579498 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9653584412327) ^ 571838 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_10856805976217 : Nat.Prime 10856805976217 := by
  apply lucas_primality 10856805976217 (3 : ZMod 10856805976217)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (397, 1), (79497437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (397, 1), (79497437, 1)] : List FactorBlock).map factorBlockValue).prod) = 10856805976217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_43
      · exact prime_fiftyEightBD_397
      · exact prime_fiftyEightBD_79497437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10856805976217) ^ 5428402988108 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10856805976217) ^ 252483859912 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10856805976217) ^ 27347118328 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10856805976217) ^ 136568 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_11047333953863 : Nat.Prime 11047333953863 := by
  apply lucas_primality 11047333953863 (5 : ZMod 11047333953863)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5523666976931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5523666976931, 1)] : List FactorBlock).map factorBlockValue).prod) = 11047333953863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5523666976931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 11047333953863) ^ 5523666976931 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11047333953863) ^ 2 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_12945434055677 : Nat.Prime 12945434055677 := by
  apply lucas_primality 12945434055677 (2 : ZMod 12945434055677)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2467, 1), (1311859957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2467, 1), (1311859957, 1)] : List FactorBlock).map factorBlockValue).prod) = 12945434055677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_2467
      · exact prime_fiftyEightBD_1311859957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12945434055677) ^ 6472717027838 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12945434055677) ^ 5247439828 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12945434055677) ^ 9868 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_14375567490331 : Nat.Prime 14375567490331 := by
  apply lucas_primality 14375567490331 (2 : ZMod 14375567490331)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (6679, 1), (1939057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (6679, 1), (1939057, 1)] : List FactorBlock).map factorBlockValue).prod) = 14375567490331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_6679
      · exact prime_fiftyEightBD_1939057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14375567490331) ^ 7187783745165 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14375567490331) ^ 4791855830110 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14375567490331) ^ 2875113498066 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14375567490331) ^ 388528851090 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14375567490331) ^ 2152353270 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14375567490331) ^ 7413690 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_15654127509043 : Nat.Prime 15654127509043 := by
  apply lucas_primality 15654127509043 (2 : ZMod 15654127509043)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1399, 1), (169538063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1399, 1), (169538063, 1)] : List FactorBlock).map factorBlockValue).prod) = 15654127509043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_1399
      · exact prime_fiftyEightBD_169538063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15654127509043) ^ 7827063754521 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15654127509043) ^ 5218042503014 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15654127509043) ^ 1423102500822 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15654127509043) ^ 11189512158 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15654127509043) ^ 92334 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_23243531552093 : Nat.Prime 23243531552093 := by
  apply lucas_primality 23243531552093 (2 : ZMod 23243531552093)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (169843, 1), (34213261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (169843, 1), (34213261, 1)] : List FactorBlock).map factorBlockValue).prod) = 23243531552093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_169843
      · exact prime_fiftyEightBD_34213261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23243531552093) ^ 11621765776046 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23243531552093) ^ 136853044 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23243531552093) ^ 679372 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_24997553723869 : Nat.Prime 24997553723869 := by
  apply lucas_primality 24997553723869 (2 : ZMod 24997553723869)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (59, 1), (127, 1), (1637, 1), (15439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (59, 1), (127, 1), (1637, 1), (15439, 1)] : List FactorBlock).map factorBlockValue).prod) = 24997553723869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_59
      · exact prime_fiftyEightBD_127
      · exact prime_fiftyEightBD_1637
      · exact prime_fiftyEightBD_15439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24997553723869) ^ 12498776861934 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24997553723869) ^ 8332517907956 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24997553723869) ^ 2272504883988 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24997553723869) ^ 423687351252 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24997553723869) ^ 196831131684 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24997553723869) ^ 15270344364 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24997553723869) ^ 1619117412 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_25616426246909 : Nat.Prime 25616426246909 := by
  apply lucas_primality 25616426246909 (2 : ZMod 25616426246909)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (521869, 1), (1753069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (521869, 1), (1753069, 1)] : List FactorBlock).map factorBlockValue).prod) = 25616426246909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_521869
      · exact prime_fiftyEightBD_1753069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25616426246909) ^ 12808213123454 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25616426246909) ^ 3659489463844 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25616426246909) ^ 49085932 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25616426246909) ^ 14612332 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_29297510625353 : Nat.Prime 29297510625353 := by
  apply lucas_primality 29297510625353 (3 : ZMod 29297510625353)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (61, 1), (38149, 1), (42533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (61, 1), (38149, 1), (42533, 1)] : List FactorBlock).map factorBlockValue).prod) = 29297510625353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_61
      · exact prime_fiftyEightBD_38149
      · exact prime_fiftyEightBD_42533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29297510625353) ^ 14648755312676 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29297510625353) ^ 791824611496 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29297510625353) ^ 480287059432 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29297510625353) ^ 767975848 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29297510625353) ^ 688818344 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_43746941503339 : Nat.Prime 43746941503339 := by
  apply lucas_primality 43746941503339 (2 : ZMod 43746941503339)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (7587051943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (7587051943, 1)] : List FactorBlock).map factorBlockValue).prod) = 43746941503339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_7587051943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43746941503339) ^ 21873470751669 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43746941503339) ^ 14582313834446 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43746941503339) ^ 1411191661398 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43746941503339) ^ 5766 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_44685545237171 : Nat.Prime 44685545237171 := by
  apply lucas_primality 44685545237171 (2 : ZMod 44685545237171)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4468554523717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4468554523717, 1)] : List FactorBlock).map factorBlockValue).prod) = 44685545237171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_4468554523717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44685545237171) ^ 22342772618585 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 44685545237171) ^ 8937109047434 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 44685545237171) ^ 10 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_48093387393001 : Nat.Prime 48093387393001 := by
  apply lucas_primality 48093387393001 (13 : ZMod 48093387393001)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (16031129131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (16031129131, 1)] : List FactorBlock).map factorBlockValue).prod) = 48093387393001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_16031129131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 48093387393001) ^ 24046693696500 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 48093387393001) ^ 16031129131000 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 48093387393001) ^ 9618677478600 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 48093387393001) ^ 3000 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_48603507691399 : Nat.Prime 48603507691399 := by
  apply lucas_primality 48603507691399 (3 : ZMod 48603507691399)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (52709, 1), (13971367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (52709, 1), (13971367, 1)] : List FactorBlock).map factorBlockValue).prod) = 48603507691399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_52709
      · exact prime_fiftyEightBD_13971367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48603507691399) ^ 24301753845699 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48603507691399) ^ 16201169230466 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48603507691399) ^ 4418500699218 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48603507691399) ^ 922110222 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48603507691399) ^ 3478794 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_57836783094107 : Nat.Prime 57836783094107 := by
  apply lucas_primality 57836783094107 (2 : ZMod 57836783094107)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (34757, 1), (2127919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (34757, 1), (2127919, 1)] : List FactorBlock).map factorBlockValue).prod) = 57836783094107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_34757
      · exact prime_fiftyEightBD_2127919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57836783094107) ^ 28918391547053 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57836783094107) ^ 3402163711418 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57836783094107) ^ 2514642743222 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57836783094107) ^ 1664032658 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57836783094107) ^ 27179974 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_77189895815441 : Nat.Prime 77189895815441 := by
  apply lucas_primality 77189895815441 (3 : ZMod 77189895815441)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (33271506817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (33271506817, 1)] : List FactorBlock).map factorBlockValue).prod) = 77189895815441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_33271506817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 77189895815441) ^ 38594947907720 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 77189895815441) ^ 15437979163088 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 77189895815441) ^ 2661720545360 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 77189895815441) ^ 2320 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_84196804605163 : Nat.Prime 84196804605163 := by
  apply lucas_primality 84196804605163 (2 : ZMod 84196804605163)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (281, 1), (1723, 1), (194521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (281, 1), (1723, 1), (194521, 1)] : List FactorBlock).map factorBlockValue).prod) = 84196804605163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_149
      · exact prime_fiftyEightBD_281
      · exact prime_fiftyEightBD_1723
      · exact prime_fiftyEightBD_194521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84196804605163) ^ 42098402302581 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84196804605163) ^ 28065601535054 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84196804605163) ^ 565079225538 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84196804605163) ^ 299632756602 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84196804605163) ^ 48866398494 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84196804605163) ^ 432841722 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_128382908113991 : Nat.Prime 128382908113991 := by
  apply lucas_primality 128382908113991 (11 : ZMod 128382908113991)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (353, 1), (36369095783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (353, 1), (36369095783, 1)] : List FactorBlock).map factorBlockValue).prod) = 128382908113991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_353
      · exact prime_fiftyEightBD_36369095783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 128382908113991) ^ 64191454056995 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 128382908113991) ^ 25676581622798 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 128382908113991) ^ 363690957830 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 128382908113991) ^ 3530 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_151854708814271 : Nat.Prime 151854708814271 := by
  apply lucas_primality 151854708814271 (11 : ZMod 151854708814271)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (197213907551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (197213907551, 1)] : List FactorBlock).map factorBlockValue).prod) = 151854708814271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_197213907551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 151854708814271) ^ 75927354407135 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 151854708814271) ^ 30370941762854 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 151854708814271) ^ 21693529830610 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 151854708814271) ^ 13804973528570 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 151854708814271) ^ 770 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_174148012875061 : Nat.Prime 174148012875061 := by
  apply lucas_primality 174148012875061 (6 : ZMod 174148012875061)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (83, 1), (8467, 1), (65557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (83, 1), (8467, 1), (65557, 1)] : List FactorBlock).map factorBlockValue).prod) = 174148012875061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_83
      · exact prime_fiftyEightBD_8467
      · exact prime_fiftyEightBD_65557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 174148012875061) ^ 87074006437530 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 174148012875061) ^ 58049337625020 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 174148012875061) ^ 34829602575012 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 174148012875061) ^ 24878287553580 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 174148012875061) ^ 2098168829820 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 174148012875061) ^ 20567853180 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 174148012875061) ^ 2656436580 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_194369240315963 : Nat.Prime 194369240315963 := by
  apply lucas_primality 194369240315963 (2 : ZMod 194369240315963)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2412899, 1), (40277119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2412899, 1), (40277119, 1)] : List FactorBlock).map factorBlockValue).prod) = 194369240315963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_2412899
      · exact prime_fiftyEightBD_40277119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 194369240315963) ^ 97184620157981 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194369240315963) ^ 80554238 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 194369240315963) ^ 4825798 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_260563343429209 : Nat.Prime 260563343429209 := by
  apply lucas_primality 260563343429209 (11 : ZMod 260563343429209)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (10856805976217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (10856805976217, 1)] : List FactorBlock).map factorBlockValue).prod) = 260563343429209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_10856805976217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 260563343429209) ^ 130281671714604 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 260563343429209) ^ 86854447809736 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 260563343429209) ^ 24 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_261780112899703 : Nat.Prime 261780112899703 := by
  apply lucas_primality 261780112899703 (3 : ZMod 261780112899703)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (113, 1), (1621, 1), (26465581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (113, 1), (1621, 1), (26465581, 1)] : List FactorBlock).map factorBlockValue).prod) = 261780112899703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_113
      · exact prime_fiftyEightBD_1621
      · exact prime_fiftyEightBD_26465581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 261780112899703) ^ 130890056449851 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 261780112899703) ^ 87260037633234 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 261780112899703) ^ 2316638167254 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 261780112899703) ^ 161492975262 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 261780112899703) ^ 9891342 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_291713898098993 : Nat.Prime 291713898098993 := by
  apply lucas_primality 291713898098993 (3 : ZMod 291713898098993)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (167, 1), (11953, 1), (314953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (167, 1), (11953, 1), (314953, 1)] : List FactorBlock).map factorBlockValue).prod) = 291713898098993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_167
      · exact prime_fiftyEightBD_11953
      · exact prime_fiftyEightBD_314953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 291713898098993) ^ 145856949049496 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 291713898098993) ^ 10059099934448 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 291713898098993) ^ 1746789808976 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 291713898098993) ^ 24405078064 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 291713898098993) ^ 926214064 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1051699207826999 : Nat.Prime 1051699207826999 := by
  apply lucas_primality 1051699207826999 (7 : ZMod 1051699207826999)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (953, 1), (551783424883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (953, 1), (551783424883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1051699207826999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_953
      · exact prime_fiftyEightBD_551783424883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1051699207826999) ^ 525849603913499 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1051699207826999) ^ 1103566849766 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1051699207826999) ^ 1906 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1261808843580893 : Nat.Prime 1261808843580893 := by
  apply lucas_primality 1261808843580893 (2 : ZMod 1261808843580893)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (269, 1), (1172684798867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (269, 1), (1172684798867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1261808843580893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_269
      · exact prime_fiftyEightBD_1172684798867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1261808843580893) ^ 630904421790446 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1261808843580893) ^ 4690739195468 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1261808843580893) ^ 1076 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1657100093079451 : Nat.Prime 1657100093079451 := by
  apply lucas_primality 1657100093079451 (3 : ZMod 1657100093079451)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11047333953863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11047333953863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1657100093079451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11047333953863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1657100093079451) ^ 828550046539725 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1657100093079451) ^ 552366697693150 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1657100093079451) ^ 331420018615890 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1657100093079451) ^ 150 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3036174527268539 : Nat.Prime 3036174527268539 := by
  apply lucas_primality 3036174527268539 (2 : ZMod 3036174527268539)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (179, 1), (379, 1), (163336757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (179, 1), (379, 1), (163336757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3036174527268539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_137
      · exact prime_fiftyEightBD_179
      · exact prime_fiftyEightBD_379
      · exact prime_fiftyEightBD_163336757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3036174527268539) ^ 1518087263634269 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3036174527268539) ^ 22161857863274 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3036174527268539) ^ 16961868867422 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3036174527268539) ^ 8011014583822 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3036174527268539) ^ 18588434 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3658785533557079 : Nat.Prime 3658785533557079 := by
  apply lucas_primality 3658785533557079 (7 : ZMod 3658785533557079)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (1168351, 1), (4004579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (1168351, 1), (4004579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3658785533557079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_1168351
      · exact prime_fiftyEightBD_4004579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3658785533557079) ^ 1829392766778539 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3658785533557079) ^ 215222678444534 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3658785533557079) ^ 159077631893786 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3658785533557079) ^ 3131580778 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3658785533557079) ^ 913650482 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3831256283251343 : Nat.Prime 3831256283251343 := by
  apply lucas_primality 3831256283251343 (5 : ZMod 3831256283251343)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (174148012875061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (174148012875061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3831256283251343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_174148012875061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3831256283251343) ^ 1915628141625671 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3831256283251343) ^ 348296025750122 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3831256283251343) ^ 22 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4980576806310011 : Nat.Prime 4980576806310011 := by
  apply lucas_primality 4980576806310011 (2 : ZMod 4980576806310011)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29297510625353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29297510625353, 1)] : List FactorBlock).map factorBlockValue).prod) = 4980576806310011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_29297510625353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4980576806310011) ^ 2490288403155005 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980576806310011) ^ 996115361262002 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980576806310011) ^ 292975106253530 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980576806310011) ^ 170 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5250005019597967 : Nat.Prime 5250005019597967 := by
  apply lucas_primality 5250005019597967 (5 : ZMod 5250005019597967)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (80287, 1), (10898412403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (80287, 1), (10898412403, 1)] : List FactorBlock).map factorBlockValue).prod) = 5250005019597967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_80287
      · exact prime_fiftyEightBD_10898412403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5250005019597967) ^ 2625002509798983 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5250005019597967) ^ 1750001673199322 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5250005019597967) ^ 65390474418 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5250005019597967) ^ 481722 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5896156873742197 : Nat.Prime 5896156873742197 := by
  apply lucas_primality 5896156873742197 (6 : ZMod 5896156873742197)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17027, 1), (28856898229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17027, 1), (28856898229, 1)] : List FactorBlock).map factorBlockValue).prod) = 5896156873742197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_17027
      · exact prime_fiftyEightBD_28856898229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5896156873742197) ^ 2948078436871098 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5896156873742197) ^ 1965385624580732 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5896156873742197) ^ 346282778748 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5896156873742197) ^ 204324 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_7206937433255723 : Nat.Prime 7206937433255723 := by
  apply lucas_primality 7206937433255723 (2 : ZMod 7206937433255723)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (179, 1), (1184182949927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (179, 1), (1184182949927, 1)] : List FactorBlock).map factorBlockValue).prod) = 7206937433255723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_179
      · exact prime_fiftyEightBD_1184182949927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7206937433255723) ^ 3603468716627861 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7206937433255723) ^ 423937496073866 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7206937433255723) ^ 40262220297518 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7206937433255723) ^ 6086 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_7829622230232541 : Nat.Prime 7829622230232541 := by
  apply lucas_primality 7829622230232541 (2 : ZMod 7829622230232541)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (120833, 1), (1079950873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (120833, 1), (1079950873, 1)] : List FactorBlock).map factorBlockValue).prod) = 7829622230232541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_120833
      · exact prime_fiftyEightBD_1079950873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7829622230232541) ^ 3914811115116270 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7829622230232541) ^ 2609874076744180 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7829622230232541) ^ 1565924446046508 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7829622230232541) ^ 64797052380 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7829622230232541) ^ 7249980 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_8691769160005693 : Nat.Prime 8691769160005693 := by
  apply lucas_primality 8691769160005693 (2 : ZMod 8691769160005693)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8527, 1), (135059, 1), (628937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8527, 1), (135059, 1), (628937, 1)] : List FactorBlock).map factorBlockValue).prod) = 8691769160005693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_8527
      · exact prime_fiftyEightBD_135059
      · exact prime_fiftyEightBD_628937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8691769160005693) ^ 4345884580002846 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8691769160005693) ^ 2897256386668564 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8691769160005693) ^ 1019323227396 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8691769160005693) ^ 64355349588 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8691769160005693) ^ 13819777116 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_8881072156967401 : Nat.Prime 8881072156967401 := by
  apply lucas_primality 8881072156967401 (7 : ZMod 8881072156967401)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 2), (13, 1), (42170333129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 2), (13, 1), (42170333129, 1)] : List FactorBlock).map factorBlockValue).prod) = 8881072156967401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_42170333129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8881072156967401) ^ 4440536078483700 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8881072156967401) ^ 2960357385655800 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8881072156967401) ^ 1776214431393480 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8881072156967401) ^ 683159396689800 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8881072156967401) ^ 210600 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_10398656254031623 : Nat.Prime 10398656254031623 := by
  apply lucas_primality 10398656254031623 (3 : ZMod 10398656254031623)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (71, 1), (241, 1), (11254030063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (71, 1), (241, 1), (11254030063, 1)] : List FactorBlock).map factorBlockValue).prod) = 10398656254031623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_241
      · exact prime_fiftyEightBD_11254030063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10398656254031623) ^ 5199328127015811 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10398656254031623) ^ 3466218751343874 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10398656254031623) ^ 146459947239882 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10398656254031623) ^ 43147951261542 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10398656254031623) ^ 923994 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_10901107400158177 : Nat.Prime 10901107400158177 := by
  apply lucas_primality 10901107400158177 (5 : ZMod 10901107400158177)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (769, 1), (3833, 1), (38524253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (769, 1), (3833, 1), (38524253, 1)] : List FactorBlock).map factorBlockValue).prod) = 10901107400158177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_769
      · exact prime_fiftyEightBD_3833
      · exact prime_fiftyEightBD_38524253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10901107400158177) ^ 5450553700079088 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10901107400158177) ^ 3633702466719392 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10901107400158177) ^ 14175692327904 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10901107400158177) ^ 2844014453472 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10901107400158177) ^ 282967392 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_13892152154109241 : Nat.Prime 13892152154109241 := by
  apply lucas_primality 13892152154109241 (7 : ZMod 13892152154109241)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (73, 1), (6599, 1), (21847141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (73, 1), (6599, 1), (21847141, 1)] : List FactorBlock).map factorBlockValue).prod) = 13892152154109241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_73
      · exact prime_fiftyEightBD_6599
      · exact prime_fiftyEightBD_21847141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13892152154109241) ^ 6946076077054620 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 13892152154109241) ^ 4630717384703080 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 13892152154109241) ^ 2778430430821848 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 13892152154109241) ^ 1262922923100840 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 13892152154109241) ^ 190303454165880 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 13892152154109241) ^ 2105190506760 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 13892152154109241) ^ 635879640 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_22430259145964359 : Nat.Prime 22430259145964359 := by
  apply lucas_primality 22430259145964359 (3 : ZMod 22430259145964359)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (47, 1), (31481, 1), (64784641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (47, 1), (31481, 1), (64784641, 1)] : List FactorBlock).map factorBlockValue).prod) = 22430259145964359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_47
      · exact prime_fiftyEightBD_31481
      · exact prime_fiftyEightBD_64784641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22430259145964359) ^ 11215129572982179 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 22430259145964359) ^ 7476753048654786 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 22430259145964359) ^ 1725404549689566 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 22430259145964359) ^ 477239556297114 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 22430259145964359) ^ 712501481718 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 22430259145964359) ^ 346228038 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_37907853364856533 : Nat.Prime 37907853364856533 := by
  apply lucas_primality 37907853364856533 (2 : ZMod 37907853364856533)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1931, 1), (124087, 1), (13183763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1931, 1), (124087, 1), (13183763, 1)] : List FactorBlock).map factorBlockValue).prod) = 37907853364856533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1931
      · exact prime_fiftyEightBD_124087
      · exact prime_fiftyEightBD_13183763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37907853364856533) ^ 18953926682428266 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37907853364856533) ^ 12635951121618844 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37907853364856533) ^ 19631203192572 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37907853364856533) ^ 305494156236 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37907853364856533) ^ 2875343964 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_73003107705436357 : Nat.Prime 73003107705436357 := by
  apply lucas_primality 73003107705436357 (2 : ZMod 73003107705436357)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (179, 1), (4855221315871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (179, 1), (4855221315871, 1)] : List FactorBlock).map factorBlockValue).prod) = 73003107705436357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_179
      · exact prime_fiftyEightBD_4855221315871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73003107705436357) ^ 36501553852718178 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 73003107705436357) ^ 24334369235145452 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 73003107705436357) ^ 10429015386490908 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 73003107705436357) ^ 407838590533164 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 73003107705436357) ^ 15036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_87905023960515547 : Nat.Prime 87905023960515547 := by
  apply lucas_primality 87905023960515547 (3 : ZMod 87905023960515547)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1039, 1), (5867, 1), (2403426307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1039, 1), (5867, 1), (2403426307, 1)] : List FactorBlock).map factorBlockValue).prod) = 87905023960515547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1039
      · exact prime_fiftyEightBD_5867
      · exact prime_fiftyEightBD_2403426307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87905023960515547) ^ 43952511980257773 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 87905023960515547) ^ 29301674653505182 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 87905023960515547) ^ 84605412859014 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 87905023960515547) ^ 14982959597838 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 87905023960515547) ^ 36574878 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_125739613191606331 : Nat.Prime 125739613191606331 := by
  apply lucas_primality 125739613191606331 (3 : ZMod 125739613191606331)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (241, 1), (225509, 1), (11017217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (241, 1), (225509, 1), (11017217, 1)] : List FactorBlock).map factorBlockValue).prod) = 125739613191606331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_241
      · exact prime_fiftyEightBD_225509
      · exact prime_fiftyEightBD_11017217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125739613191606331) ^ 62869806595803165 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 125739613191606331) ^ 41913204397202110 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 125739613191606331) ^ 25147922638321266 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 125739613191606331) ^ 17962801884515190 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 125739613191606331) ^ 521741133575130 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 125739613191606331) ^ 557581352370 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 125739613191606331) ^ 11413010490 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_130716832882869293 : Nat.Prime 130716832882869293 := by
  apply lucas_primality 130716832882869293 (2 : ZMod 130716832882869293)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (28111, 1), (8485445789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (28111, 1), (8485445789, 1)] : List FactorBlock).map factorBlockValue).prod) = 130716832882869293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_137
      · exact prime_fiftyEightBD_28111
      · exact prime_fiftyEightBD_8485445789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 130716832882869293) ^ 65358416441434646 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 130716832882869293) ^ 954137466298316 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 130716832882869293) ^ 4650024292372 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 130716832882869293) ^ 15404828 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_252361768716178601 : Nat.Prime 252361768716178601 := by
  apply lucas_primality 252361768716178601 (6 : ZMod 252361768716178601)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (1261808843580893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (1261808843580893, 1)] : List FactorBlock).map factorBlockValue).prod) = 252361768716178601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_1261808843580893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 252361768716178601) ^ 126180884358089300 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 252361768716178601) ^ 50472353743235720 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 252361768716178601) ^ 200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_351620095842062189 : Nat.Prime 351620095842062189 := by
  apply lucas_primality 351620095842062189 (2 : ZMod 351620095842062189)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (87905023960515547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (87905023960515547, 1)] : List FactorBlock).map factorBlockValue).prod) = 351620095842062189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_87905023960515547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 351620095842062189) ^ 175810047921031094 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 351620095842062189) ^ 4 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_352644545742191579 : Nat.Prime 352644545742191579 := by
  apply lucas_primality 352644545742191579 (2 : ZMod 352644545742191579)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (131, 1), (409, 1), (49117671373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (131, 1), (409, 1), (49117671373, 1)] : List FactorBlock).map factorBlockValue).prod) = 352644545742191579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_67
      · exact prime_fiftyEightBD_131
      · exact prime_fiftyEightBD_409
      · exact prime_fiftyEightBD_49117671373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 352644545742191579) ^ 176322272871095789 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 352644545742191579) ^ 5263351428987934 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 352644545742191579) ^ 2691943097268638 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 352644545742191579) ^ 862211603281642 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 352644545742191579) ^ 7179586 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_538326219503144617 : Nat.Prime 538326219503144617 := by
  apply lucas_primality 538326219503144617 (7 : ZMod 538326219503144617)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (22430259145964359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (22430259145964359, 1)] : List FactorBlock).map factorBlockValue).prod) = 538326219503144617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_22430259145964359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 538326219503144617) ^ 269163109751572308 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 538326219503144617) ^ 179442073167714872 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 538326219503144617) ^ 24 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_692552461407348601 : Nat.Prime 692552461407348601 := by
  apply lucas_primality 692552461407348601 (7 : ZMod 692552461407348601)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (23, 1), (29303, 1), (570873983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (23, 1), (29303, 1), (570873983, 1)] : List FactorBlock).map factorBlockValue).prod) = 692552461407348601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_29303
      · exact prime_fiftyEightBD_570873983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 692552461407348601) ^ 346276230703674300 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 692552461407348601) ^ 230850820469116200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 692552461407348601) ^ 138510492281469720 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 692552461407348601) ^ 30110976582928200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 692552461407348601) ^ 23634182896200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 692552461407348601) ^ 1213144200 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_783192609232504873 : Nat.Prime 783192609232504873 := by
  apply lucas_primality 783192609232504873 (5 : ZMod 783192609232504873)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5393, 1), (6050996733671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5393, 1), (6050996733671, 1)] : List FactorBlock).map factorBlockValue).prod) = 783192609232504873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5393
      · exact prime_fiftyEightBD_6050996733671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 783192609232504873) ^ 391596304616252436 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 783192609232504873) ^ 261064203077501624 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 783192609232504873) ^ 145223921608104 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 783192609232504873) ^ 129432 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_833972774026843727 : Nat.Prime 833972774026843727 := by
  apply lucas_primality 833972774026843727 (5 : ZMod 833972774026843727)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37907853364856533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37907853364856533, 1)] : List FactorBlock).map factorBlockValue).prod) = 833972774026843727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_37907853364856533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 833972774026843727) ^ 416986387013421863 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 833972774026843727) ^ 75815706729713066 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 833972774026843727) ^ 22 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_910929036828961013 : Nat.Prime 910929036828961013 := by
  apply lucas_primality 910929036828961013 (2 : ZMod 910929036828961013)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (587, 1), (2167371819661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (587, 1), (2167371819661, 1)] : List FactorBlock).map factorBlockValue).prod) = 910929036828961013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_179
      · exact prime_fiftyEightBD_587
      · exact prime_fiftyEightBD_2167371819661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 910929036828961013) ^ 455464518414480506 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 910929036828961013) ^ 5088989032564028 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 910929036828961013) ^ 1551838222877276 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 910929036828961013) ^ 420292 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1027294188385307891 : Nat.Prime 1027294188385307891 := by
  apply lucas_primality 1027294188385307891 (2 : ZMod 1027294188385307891)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (331, 1), (1277, 1), (4585641199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (331, 1), (1277, 1), (4585641199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027294188385307891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_53
      · exact prime_fiftyEightBD_331
      · exact prime_fiftyEightBD_1277
      · exact prime_fiftyEightBD_4585641199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1027294188385307891) ^ 513647094192653945 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1027294188385307891) ^ 205458837677061578 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1027294188385307891) ^ 19382909214817130 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1027294188385307891) ^ 3103607819895190 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1027294188385307891) ^ 804459035540570 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1027294188385307891) ^ 224024110 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1149816502783782209 : Nat.Prime 1149816502783782209 := by
  apply lucas_primality 1149816502783782209 (3 : ZMod 1149816502783782209)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (29243, 1), (614365244879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (29243, 1), (614365244879, 1)] : List FactorBlock).map factorBlockValue).prod) = 1149816502783782209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_29243
      · exact prime_fiftyEightBD_614365244879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1149816502783782209) ^ 574908251391891104 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1149816502783782209) ^ 39319375672256 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1149816502783782209) ^ 1871552 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1156932237508899563 : Nat.Prime 1156932237508899563 := by
  apply lucas_primality 1156932237508899563 (2 : ZMod 1156932237508899563)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (911, 1), (2237, 1), (9788036227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (911, 1), (2237, 1), (9788036227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1156932237508899563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_911
      · exact prime_fiftyEightBD_2237
      · exact prime_fiftyEightBD_9788036227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1156932237508899563) ^ 578466118754449781 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1156932237508899563) ^ 39894215086513778 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1156932237508899563) ^ 1269958548308342 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1156932237508899563) ^ 517180258162226 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1156932237508899563) ^ 118198606 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1317699744834545927 : Nat.Prime 1317699744834545927 := by
  apply lucas_primality 1317699744834545927 (10 : ZMod 1317699744834545927)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (3036174527268539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (3036174527268539, 1)] : List FactorBlock).map factorBlockValue).prod) = 1317699744834545927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_3036174527268539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1317699744834545927) ^ 658849872417272963 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1317699744834545927) ^ 188242820690649418 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1317699744834545927) ^ 42506443381759546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1317699744834545927) ^ 434 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1601564002091546359 : Nat.Prime 1601564002091546359 := by
  apply lucas_primality 1601564002091546359 (6 : ZMod 1601564002091546359)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (139, 1), (8329, 1), (36343, 1), (275827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (139, 1), (8329, 1), (36343, 1), (275827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1601564002091546359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_139
      · exact prime_fiftyEightBD_8329
      · exact prime_fiftyEightBD_36343
      · exact prime_fiftyEightBD_275827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1601564002091546359) ^ 800782001045773179 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1601564002091546359) ^ 533854667363848786 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1601564002091546359) ^ 69633217482241146 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1601564002091546359) ^ 11522043180514722 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1601564002091546359) ^ 192287669839302 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1601564002091546359) ^ 44068018658106 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1601564002091546359) ^ 5806407647154 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1749897698291900257 : Nat.Prime 1749897698291900257 := by
  apply lucas_primality 1749897698291900257 (5 : ZMod 1749897698291900257)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (1657100093079451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (1657100093079451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1749897698291900257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_1657100093079451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1749897698291900257) ^ 874948849145950128 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749897698291900257) ^ 583299232763966752 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749897698291900257) ^ 159081608935627296 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749897698291900257) ^ 1056 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1889332692958856777 : Nat.Prime 1889332692958856777 := by
  apply lucas_primality 1889332692958856777 (3 : ZMod 1889332692958856777)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (13892152154109241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (13892152154109241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1889332692958856777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_13892152154109241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1889332692958856777) ^ 944666346479428388 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1889332692958856777) ^ 111137217232873928 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1889332692958856777) ^ 136 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1974294409982615233 : Nat.Prime 1974294409982615233 := by
  apply lucas_primality 1974294409982615233 (11 : ZMod 1974294409982615233)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (251, 1), (1095443, 1), (37397897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (251, 1), (1095443, 1), (37397897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1974294409982615233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_251
      · exact prime_fiftyEightBD_1095443
      · exact prime_fiftyEightBD_37397897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1974294409982615233) ^ 987147204991307616 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1974294409982615233) ^ 658098136660871744 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1974294409982615233) ^ 7865714780807232 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1974294409982615233) ^ 1802279452224 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1974294409982615233) ^ 52791589056 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2313864475017799127 : Nat.Prime 2313864475017799127 := by
  apply lucas_primality 2313864475017799127 (5 : ZMod 2313864475017799127)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1156932237508899563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1156932237508899563, 1)] : List FactorBlock).map factorBlockValue).prod) = 2313864475017799127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_1156932237508899563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2313864475017799127) ^ 1156932237508899563 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2313864475017799127) ^ 2 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2571300254725544647 : Nat.Prime 2571300254725544647 := by
  apply lucas_primality 2571300254725544647 (3 : ZMod 2571300254725544647)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (523, 1), (14375567490331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (523, 1), (14375567490331, 1)] : List FactorBlock).map factorBlockValue).prod) = 2571300254725544647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_19
      · exact prime_fiftyEightBD_523
      · exact prime_fiftyEightBD_14375567490331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2571300254725544647) ^ 1285650127362772323 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2571300254725544647) ^ 857100084908514882 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2571300254725544647) ^ 135331592353976034 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2571300254725544647) ^ 4916444081693202 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2571300254725544647) ^ 178866 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_4995662934552754817 : Nat.Prime 4995662934552754817 := by
  apply lucas_primality 4995662934552754817 (3 : ZMod 4995662934552754817)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (11, 1), (73, 1), (48603507691399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (11, 1), (73, 1), (48603507691399, 1)] : List FactorBlock).map factorBlockValue).prod) = 4995662934552754817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_73
      · exact prime_fiftyEightBD_48603507691399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4995662934552754817) ^ 2497831467276377408 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4995662934552754817) ^ 454151175868432256 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4995662934552754817) ^ 68433738829489792 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4995662934552754817) ^ 102784 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5225681717713335889 : Nat.Prime 5225681717713335889 := by
  apply lucas_primality 5225681717713335889 (7 : ZMod 5225681717713335889)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (7041449, 1), (572632397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (7041449, 1), (572632397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5225681717713335889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7041449
      · exact prime_fiftyEightBD_572632397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5225681717713335889) ^ 2612840858856667944 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5225681717713335889) ^ 1741893905904445296 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5225681717713335889) ^ 742131586512 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5225681717713335889) ^ 9125717904 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_5592182895981950701 : Nat.Prime 5592182895981950701 := by
  apply lucas_primality 5592182895981950701 (2 : ZMod 5592182895981950701)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (3023, 1), (11593, 1), (11731, 1), (45341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (3023, 1), (11593, 1), (11731, 1), (45341, 1)] : List FactorBlock).map factorBlockValue).prod) = 5592182895981950701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_3023
      · exact prime_fiftyEightBD_11593
      · exact prime_fiftyEightBD_11731
      · exact prime_fiftyEightBD_45341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5592182895981950701) ^ 2796091447990975350 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592182895981950701) ^ 1864060965327316900 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592182895981950701) ^ 1118436579196390140 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592182895981950701) ^ 1849878563010900 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592182895981950701) ^ 482375821269900 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592182895981950701) ^ 476701295369700 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592182895981950701) ^ 123336117332700 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_11335996157753140663 : Nat.Prime 11335996157753140663 := by
  apply lucas_primality 11335996157753140663 (5 : ZMod 11335996157753140663)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1889332692958856777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1889332692958856777, 1)] : List FactorBlock).map factorBlockValue).prod) = 11335996157753140663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1889332692958856777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11335996157753140663) ^ 5667998078876570331 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11335996157753140663) ^ 3778665385917713554 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11335996157753140663) ^ 6 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_18040482329970856477 : Nat.Prime 18040482329970856477 := by
  apply lucas_primality 18040482329970856477 (2 : ZMod 18040482329970856477)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (503, 1), (272249, 1), (1568319637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (503, 1), (272249, 1), (1568319637, 1)] : List FactorBlock).map factorBlockValue).prod) = 18040482329970856477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_503
      · exact prime_fiftyEightBD_272249
      · exact prime_fiftyEightBD_1568319637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18040482329970856477) ^ 9020241164985428238 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18040482329970856477) ^ 6013494109990285492 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18040482329970856477) ^ 2577211761424408068 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18040482329970856477) ^ 35865770039703492 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18040482329970856477) ^ 66264641302524 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18040482329970856477) ^ 11503064748 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_23629799890841808739 : Nat.Prime 23629799890841808739 := by
  apply lucas_primality 23629799890841808739 (2 : ZMod 23629799890841808739)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (503, 1), (7829622230232541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (503, 1), (7829622230232541, 1)] : List FactorBlock).map factorBlockValue).prod) = 23629799890841808739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_503
      · exact prime_fiftyEightBD_7829622230232541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23629799890841808739) ^ 11814899945420904369 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23629799890841808739) ^ 7876599963613936246 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23629799890841808739) ^ 46977733381395246 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 23629799890841808739) ^ 3018 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_27998363172670404113 : Nat.Prime 27998363172670404113 := by
  apply lucas_primality 27998363172670404113 (3 : ZMod 27998363172670404113)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1749897698291900257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1749897698291900257, 1)] : List FactorBlock).map factorBlockValue).prod) = 27998363172670404113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_1749897698291900257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 27998363172670404113) ^ 13999181586335202056 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 27998363172670404113) ^ 16 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_41279283483408329587 : Nat.Prime 41279283483408329587 := by
  apply lucas_primality 41279283483408329587 (2 : ZMod 41279283483408329587)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1471, 1), (153887, 1), (30392490803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1471, 1), (153887, 1), (30392490803, 1)] : List FactorBlock).map factorBlockValue).prod) = 41279283483408329587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1471
      · exact prime_fiftyEightBD_153887
      · exact prime_fiftyEightBD_30392490803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41279283483408329587) ^ 20639641741704164793 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41279283483408329587) ^ 13759761161136109862 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41279283483408329587) ^ 28062055393207566 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41279283483408329587) ^ 268244123827278 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41279283483408329587) ^ 1358206662 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_45663852802687124591 : Nat.Prime 45663852802687124591 := by
  apply lucas_primality 45663852802687124591 (11 : ZMod 45663852802687124591)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (17, 1), (30367, 1), (420319, 1), (1618823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (17, 1), (30367, 1), (420319, 1), (1618823, 1)] : List FactorBlock).map factorBlockValue).prod) = 45663852802687124591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_17
      · exact prime_fiftyEightBD_30367
      · exact prime_fiftyEightBD_420319
      · exact prime_fiftyEightBD_1618823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 45663852802687124591) ^ 22831926401343562295 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45663852802687124591) ^ 9132770560537424918 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45663852802687124591) ^ 3512604061745163430 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45663852802687124591) ^ 2686108988393360270 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45663852802687124591) ^ 1503732762626770 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45663852802687124591) ^ 108640943670610 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45663852802687124591) ^ 28208057831330 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_88291359214560546857 : Nat.Prime 88291359214560546857 := by
  apply lucas_primality 88291359214560546857 (3 : ZMod 88291359214560546857)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (71, 1), (829, 1), (527809, 1), (957557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (71, 1), (829, 1), (527809, 1), (957557, 1)] : List FactorBlock).map factorBlockValue).prod) = 88291359214560546857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_53
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_829
      · exact prime_fiftyEightBD_527809
      · exact prime_fiftyEightBD_957557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88291359214560546857) ^ 44145679607280273428 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88291359214560546857) ^ 12613051316365792408 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88291359214560546857) ^ 1665874702161519752 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88291359214560546857) ^ 1243540270627613336 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88291359214560546857) ^ 106503448992232264 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88291359214560546857) ^ 167278995270184 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88291359214560546857) ^ 92204807875208 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_192569379142793730373 : Nat.Prime 192569379142793730373 := by
  apply lucas_primality 192569379142793730373 (11 : ZMod 192569379142793730373)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (601, 1), (28123, 1), (316481705699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (601, 1), (28123, 1), (316481705699, 1)] : List FactorBlock).map factorBlockValue).prod) = 192569379142793730373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_601
      · exact prime_fiftyEightBD_28123
      · exact prime_fiftyEightBD_316481705699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 192569379142793730373) ^ 96284689571396865186 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 192569379142793730373) ^ 64189793047597910124 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 192569379142793730373) ^ 320414940337427172 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 192569379142793730373) ^ 6847398184503564 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (11 : ZMod 192569379142793730373) ^ 608469228 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_350596473462933456587 : Nat.Prime 350596473462933456587 := by
  apply lucas_primality 350596473462933456587 (2 : ZMod 350596473462933456587)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42138401, 1), (4160059057093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42138401, 1), (4160059057093, 1)] : List FactorBlock).map factorBlockValue).prod) = 350596473462933456587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_42138401
      · exact prime_fiftyEightBD_4160059057093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 350596473462933456587) ^ 175298236731466728293 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 350596473462933456587) ^ 8320118114186 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 350596473462933456587) ^ 84276802 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_555378625749357759949 : Nat.Prime 555378625749357759949 := by
  apply lucas_primality 555378625749357759949 (2 : ZMod 555378625749357759949)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (549683, 1), (84196804605163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (549683, 1), (84196804605163, 1)] : List FactorBlock).map factorBlockValue).prod) = 555378625749357759949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_549683
      · exact prime_fiftyEightBD_84196804605163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 555378625749357759949) ^ 277689312874678879974 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 555378625749357759949) ^ 185126208583119253316 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 555378625749357759949) ^ 1010361655261956 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 555378625749357759949) ^ 6596196 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_581887944885731043359 : Nat.Prime 581887944885731043359 := by
  apply lucas_primality 581887944885731043359 (7 : ZMod 581887944885731043359)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (887, 1), (2591, 1), (9028273, 1), (14022119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (887, 1), (2591, 1), (9028273, 1), (14022119, 1)] : List FactorBlock).map factorBlockValue).prod) = 581887944885731043359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_887
      · exact prime_fiftyEightBD_2591
      · exact prime_fiftyEightBD_9028273
      · exact prime_fiftyEightBD_14022119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 581887944885731043359) ^ 290943972442865521679 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 581887944885731043359) ^ 656017976195863634 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 581887944885731043359) ^ 224580449589243938 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 581887944885731043359) ^ 64451744523646 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 581887944885731043359) ^ 41497860978482 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1495471238031852521227 : Nat.Prime 1495471238031852521227 := by
  apply lucas_primality 1495471238031852521227 (5 : ZMod 1495471238031852521227)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (1697, 1), (6165581, 1), (64557187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (1697, 1), (6165581, 1), (64557187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1495471238031852521227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_41
      · exact prime_fiftyEightBD_1697
      · exact prime_fiftyEightBD_6165581
      · exact prime_fiftyEightBD_64557187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1495471238031852521227) ^ 747735619015926260613 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1495471238031852521227) ^ 498490412677284173742 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1495471238031852521227) ^ 36474908244679329786 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1495471238031852521227) ^ 881244100195552458 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1495471238031852521227) ^ 242551551594546 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1495471238031852521227) ^ 23165061978798 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1578911213453177529197 : Nat.Prime 1578911213453177529197 := by
  apply lucas_primality 1578911213453177529197 (2 : ZMod 1578911213453177529197)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5407, 1), (73003107705436357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5407, 1), (73003107705436357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1578911213453177529197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5407
      · exact prime_fiftyEightBD_73003107705436357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1578911213453177529197) ^ 789455606726588764598 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1578911213453177529197) ^ 292012430821745428 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1578911213453177529197) ^ 21628 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_7754566017499778282737 : Nat.Prime 7754566017499778282737 := by
  apply lucas_primality 7754566017499778282737 (10 : ZMod 7754566017499778282737)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (18679, 1), (21803, 1), (208367, 1), (271969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (18679, 1), (21803, 1), (208367, 1), (271969, 1)] : List FactorBlock).map factorBlockValue).prod) = 7754566017499778282737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_18679
      · exact prime_fiftyEightBD_21803
      · exact prime_fiftyEightBD_208367
      · exact prime_fiftyEightBD_271969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7754566017499778282737) ^ 3877283008749889141368 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7754566017499778282737) ^ 2584855339166592760912 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7754566017499778282737) ^ 1107795145357111183248 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7754566017499778282737) ^ 415148884710090384 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7754566017499778282737) ^ 355665092762453712 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7754566017499778282737) ^ 37215902794107408 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7754566017499778282737) ^ 28512683495176944 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_23416717843332899152399 : Nat.Prime 23416717843332899152399 := by
  apply lucas_primality 23416717843332899152399 (3 : ZMod 23416717843332899152399)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (59, 1), (4969, 1), (24653459, 1), (59997533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (59, 1), (4969, 1), (24653459, 1), (59997533, 1)] : List FactorBlock).map factorBlockValue).prod) = 23416717843332899152399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_59
      · exact prime_fiftyEightBD_4969
      · exact prime_fiftyEightBD_24653459
      · exact prime_fiftyEightBD_59997533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23416717843332899152399) ^ 11708358921666449576199 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23416717843332899152399) ^ 7805572614444299717466 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23416717843332899152399) ^ 396893522768354222922 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23416717843332899152399) ^ 4712561449654437342 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23416717843332899152399) ^ 949834984345722 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23416717843332899152399) ^ 390294678338406 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_29885046937279666018013 : Nat.Prime 29885046937279666018013 := by
  apply lucas_primality 29885046937279666018013 (2 : ZMod 29885046937279666018013)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (74219, 1), (5205721, 1), (2762484971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (74219, 1), (5205721, 1), (2762484971, 1)] : List FactorBlock).map factorBlockValue).prod) = 29885046937279666018013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_74219
      · exact prime_fiftyEightBD_5205721
      · exact prime_fiftyEightBD_2762484971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29885046937279666018013) ^ 14942523468639833009006 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 29885046937279666018013) ^ 4269292419611380859716 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 29885046937279666018013) ^ 402660328720134548 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 29885046937279666018013) ^ 5740808417754172 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 29885046937279666018013) ^ 10818175393172 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_38086189057143431879657 : Nat.Prime 38086189057143431879657 := by
  apply lucas_primality 38086189057143431879657 (3 : ZMod 38086189057143431879657)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (1123, 1), (96959, 1), (561667, 1), (2103919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (1123, 1), (96959, 1), (561667, 1), (2103919, 1)] : List FactorBlock).map factorBlockValue).prod) = 38086189057143431879657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_1123
      · exact prime_fiftyEightBD_96959
      · exact prime_fiftyEightBD_561667
      · exact prime_fiftyEightBD_2103919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38086189057143431879657) ^ 19043094528571715939828 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 38086189057143431879657) ^ 1029356461003876537288 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 38086189057143431879657) ^ 33914683042870375672 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 38086189057143431879657) ^ 392807156191208984 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 38086189057143431879657) ^ 67809198434558968 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 38086189057143431879657) ^ 18102497794422424 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_41402947762262538606893 : Nat.Prime 41402947762262538606893 := by
  apply lucas_primality 41402947762262538606893 (2 : ZMod 41402947762262538606893)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (37181, 1), (1353827, 1), (1136078809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (37181, 1), (1353827, 1), (1136078809, 1)] : List FactorBlock).map factorBlockValue).prod) = 41402947762262538606893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_181
      · exact prime_fiftyEightBD_37181
      · exact prime_fiftyEightBD_1353827
      · exact prime_fiftyEightBD_1136078809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41402947762262538606893) ^ 20701473881131269303446 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41402947762262538606893) ^ 228745567747306843132 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41402947762262538606893) ^ 1113551216004479132 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41402947762262538606893) ^ 30582155446938596 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41402947762262538606893) ^ 36443728581388 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_52977622152592418666123 : Nat.Prime 52977622152592418666123 := by
  apply lucas_primality 52977622152592418666123 (2 : ZMod 52977622152592418666123)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5045483, 1), (5250005019597967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5045483, 1), (5250005019597967, 1)] : List FactorBlock).map factorBlockValue).prod) = 52977622152592418666123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5045483
      · exact prime_fiftyEightBD_5250005019597967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52977622152592418666123) ^ 26488811076296209333061 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52977622152592418666123) ^ 10500010039195934 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52977622152592418666123) ^ 10090966 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_92372563472556486436949 : Nat.Prime 92372563472556486436949 := by
  apply lucas_primality 92372563472556486436949 (2 : ZMod 92372563472556486436949)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (79, 2), (149, 1), (541, 1), (328961, 1), (7344247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (79, 2), (149, 1), (541, 1), (328961, 1), (7344247, 1)] : List FactorBlock).map factorBlockValue).prod) = 92372563472556486436949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_19
      · exact prime_fiftyEightBD_79
      · exact prime_fiftyEightBD_149
      · exact prime_fiftyEightBD_541
      · exact prime_fiftyEightBD_328961
      · exact prime_fiftyEightBD_7344247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92372563472556486436949) ^ 46186281736278243218474 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 92372563472556486436949) ^ 4861713866976657180892 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 92372563472556486436949) ^ 1169272955348816284012 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 92372563472556486436949) ^ 619950090419842190852 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 92372563472556486436949) ^ 170744109930788329828 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 92372563472556486436949) ^ 280800956564931668 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 92372563472556486436949) ^ 12577540416676684 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_104067576869728920078461 : Nat.Prime 104067576869728920078461 := by
  apply lucas_primality 104067576869728920078461 (2 : ZMod 104067576869728920078461)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (1481, 1), (4289317, 1), (19049070493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (1481, 1), (4289317, 1), (19049070493, 1)] : List FactorBlock).map factorBlockValue).prod) = 104067576869728920078461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_43
      · exact prime_fiftyEightBD_1481
      · exact prime_fiftyEightBD_4289317
      · exact prime_fiftyEightBD_19049070493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104067576869728920078461) ^ 52033788434864460039230 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104067576869728920078461) ^ 20813515373945784015692 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104067576869728920078461) ^ 2420176206272765583220 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104067576869728920078461) ^ 70268451633848021660 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104067576869728920078461) ^ 24262039124114380 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104067576869728920078461) ^ 5463131490220 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_149319029497251238852289 : Nat.Prime 149319029497251238852289 := by
  apply lucas_primality 149319029497251238852289 (3 : ZMod 149319029497251238852289)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (29, 1), (79, 1), (411779, 1), (2473124050003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (29, 1), (79, 1), (411779, 1), (2473124050003, 1)] : List FactorBlock).map factorBlockValue).prod) = 149319029497251238852289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_79
      · exact prime_fiftyEightBD_411779
      · exact prime_fiftyEightBD_2473124050003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 149319029497251238852289) ^ 74659514748625619426144 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 149319029497251238852289) ^ 5148932051629353063872 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 149319029497251238852289) ^ 1890114297433559985472 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 149319029497251238852289) ^ 362619340707639872 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 149319029497251238852289) ^ 60376684096 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_271943935935577573598803 : Nat.Prime 271943935935577573598803 := by
  apply lucas_primality 271943935935577573598803 (2 : ZMod 271943935935577573598803)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4710915431, 1), (3207019243319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4710915431, 1), (3207019243319, 1)] : List FactorBlock).map factorBlockValue).prod) = 271943935935577573598803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_4710915431
      · exact prime_fiftyEightBD_3207019243319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 271943935935577573598803) ^ 135971967967788786799401 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 271943935935577573598803) ^ 90647978645192524532934 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 271943935935577573598803) ^ 57726346379742 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 271943935935577573598803) ^ 84796477758 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_310121021373619215219703 : Nat.Prime 310121021373619215219703 := by
  apply lucas_primality 310121021373619215219703 (3 : ZMod 310121021373619215219703)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (719599, 1), (151854708814271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (719599, 1), (151854708814271, 1)] : List FactorBlock).map factorBlockValue).prod) = 310121021373619215219703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_43
      · exact prime_fiftyEightBD_719599
      · exact prime_fiftyEightBD_151854708814271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 310121021373619215219703) ^ 155060510686809607609851 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 310121021373619215219703) ^ 103373673791206405073234 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 310121021373619215219703) ^ 28192820124874474110882 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 310121021373619215219703) ^ 7212116776130679423714 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 310121021373619215219703) ^ 430963663614901098 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 310121021373619215219703) ^ 2042221962 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_335011428728985616441241 : Nat.Prime 335011428728985616441241 := by
  apply lucas_primality 335011428728985616441241 (3 : ZMod 335011428728985616441241)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (208099, 1), (3658785533557079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (208099, 1), (3658785533557079, 1)] : List FactorBlock).map factorBlockValue).prod) = 335011428728985616441241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_208099
      · exact prime_fiftyEightBD_3658785533557079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335011428728985616441241) ^ 167505714364492808220620 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335011428728985616441241) ^ 67002285745797123288248 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335011428728985616441241) ^ 30455584429907783312840 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335011428728985616441241) ^ 1609865634765114760 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335011428728985616441241) ^ 91563560 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_473442233132395895465623 : Nat.Prime 473442233132395895465623 := by
  apply lucas_primality 473442233132395895465623 (3 : ZMod 473442233132395895465623)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3469, 1), (12413, 1), (261780112899703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3469, 1), (12413, 1), (261780112899703, 1)] : List FactorBlock).map factorBlockValue).prod) = 473442233132395895465623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_3469
      · exact prime_fiftyEightBD_12413
      · exact prime_fiftyEightBD_261780112899703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 473442233132395895465623) ^ 236721116566197947732811 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 473442233132395895465623) ^ 157814077710798631821874 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 473442233132395895465623) ^ 67634604733199413637946 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 473442233132395895465623) ^ 136478014739808560238 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 473442233132395895465623) ^ 38140838889260927694 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (3 : ZMod 473442233132395895465623) ^ 1808549274 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1249138888386259074882211 : Nat.Prime 1249138888386259074882211 := by
  apply lucas_primality 1249138888386259074882211 (10 : ZMod 1249138888386259074882211)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (61, 1), (89, 1), (199, 1), (641, 1), (1541678868883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (61, 1), (89, 1), (199, 1), (641, 1), (1541678868883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249138888386259074882211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_61
      · exact prime_fiftyEightBD_89
      · exact prime_fiftyEightBD_199
      · exact prime_fiftyEightBD_641
      · exact prime_fiftyEightBD_1541678868883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1249138888386259074882211) ^ 624569444193129537441105 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 416379629462086358294070 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 249827777677251814976442 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 96087606798943005760170 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 20477686694856706145610 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 14035268408834371627890 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 6277079841136980275790 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 1948734615267174843810 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 1249138888386259074882211) ^ 810245838870 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1504255331314329097634287 : Nat.Prime 1504255331314329097634287 := by
  apply lucas_primality 1504255331314329097634287 (6 : ZMod 1504255331314329097634287)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (47, 1), (71, 1), (503, 1), (26539, 1), (18823066411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (47, 1), (71, 1), (503, 1), (26539, 1), (18823066411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1504255331314329097634287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_47
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_503
      · exact prime_fiftyEightBD_26539
      · exact prime_fiftyEightBD_18823066411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1504255331314329097634287) ^ 752127665657164548817143 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 501418443771443032544762 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 115711948562640699818022 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 65402405709318656418882 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 32005432581155938247538 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 21186694807244071797666 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 2990567259074212917762 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 56680934900121673674 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1504255331314329097634287) ^ 79915530151626 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1687124281024596297501697 : Nat.Prime 1687124281024596297501697 := by
  apply lucas_primality 1687124281024596297501697 (5 : ZMod 1687124281024596297501697)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (13, 1), (61, 1), (692552461407348601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (13, 1), (61, 1), (692552461407348601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1687124281024596297501697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_13
      · exact prime_fiftyEightBD_61
      · exact prime_fiftyEightBD_692552461407348601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1687124281024596297501697) ^ 843562140512298148750848 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1687124281024596297501697) ^ 562374760341532099167232 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1687124281024596297501697) ^ 129778790848045869038592 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1687124281024596297501697) ^ 27657775098763873729536 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1687124281024596297501697) ^ 2436096 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_1710737202254414388036299 : Nat.Prime 1710737202254414388036299 := by
  apply lucas_primality 1710737202254414388036299 (2 : ZMod 1710737202254414388036299)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2371, 1), (75689051, 1), (4766380291669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2371, 1), (75689051, 1), (4766380291669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1710737202254414388036299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_2371
      · exact prime_fiftyEightBD_75689051
      · exact prime_fiftyEightBD_4766380291669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1710737202254414388036299) ^ 855368601127207194018149 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1710737202254414388036299) ^ 721525601963059632238 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1710737202254414388036299) ^ 22602175343094398 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1710737202254414388036299) ^ 358917479842 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_9712674118691741064540931 : Nat.Prime 9712674118691741064540931 := by
  apply lucas_primality 9712674118691741064540931 (2 : ZMod 9712674118691741064540931)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (223, 1), (18808417, 1), (77189895815441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (223, 1), (18808417, 1), (77189895815441, 1)] : List FactorBlock).map factorBlockValue).prod) = 9712674118691741064540931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_223
      · exact prime_fiftyEightBD_18808417
      · exact prime_fiftyEightBD_77189895815441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9712674118691741064540931) ^ 4856337059345870532270465 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9712674118691741064540931) ^ 3237558039563913688180310 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9712674118691741064540931) ^ 1942534823738348212908186 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9712674118691741064540931) ^ 43554592460501081006910 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9712674118691741064540931) ^ 516400403005300290 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9712674118691741064540931) ^ 125828309730 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_22328713538900583495818617 : Nat.Prime 22328713538900583495818617 := by
  apply lucas_primality 22328713538900583495818617 (10 : ZMod 22328713538900583495818617)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (310121021373619215219703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (310121021373619215219703, 1)] : List FactorBlock).map factorBlockValue).prod) = 22328713538900583495818617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_310121021373619215219703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 22328713538900583495818617) ^ 11164356769450291747909308 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 22328713538900583495818617) ^ 7442904512966861165272872 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (10 : ZMod 22328713538900583495818617) ^ 72 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_45501976959498136639455191 : Nat.Prime 45501976959498136639455191 := by
  apply lucas_primality 45501976959498136639455191 (7 : ZMod 45501976959498136639455191)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (71, 1), (8392456213, 1), (694208853823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (71, 1), (8392456213, 1), (694208853823, 1)] : List FactorBlock).map factorBlockValue).prod) = 45501976959498136639455191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_8392456213
      · exact prime_fiftyEightBD_694208853823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45501976959498136639455191) ^ 22750988479749068319727595 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 45501976959498136639455191) ^ 9100395391899627327891038 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 45501976959498136639455191) ^ 4136543359954376058132290 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 45501976959498136639455191) ^ 640872914922508966752890 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 45501976959498136639455191) ^ 5421771148357630 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (7 : ZMod 45501976959498136639455191) ^ 65545083023530 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_56623847463223527593442587 : Nat.Prime 56623847463223527593442587 := by
  apply lucas_primality 56623847463223527593442587 (2 : ZMod 56623847463223527593442587)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (401, 1), (84659, 1), (833972774026843727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (401, 1), (84659, 1), (833972774026843727, 1)] : List FactorBlock).map factorBlockValue).prod) = 56623847463223527593442587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_401
      · exact prime_fiftyEightBD_84659
      · exact prime_fiftyEightBD_833972774026843727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56623847463223527593442587) ^ 28311923731611763796721293 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 56623847463223527593442587) ^ 141206602152677126168186 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 56623847463223527593442587) ^ 668846164769528669054 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 56623847463223527593442587) ^ 67896518 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_168067351171479637048183757 : Nat.Prime 168067351171479637048183757 := by
  apply lucas_primality 168067351171479637048183757 (2 : ZMod 168067351171479637048183757)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (401, 1), (20051, 1), (5225681717713335889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (401, 1), (20051, 1), (5225681717713335889, 1)] : List FactorBlock).map factorBlockValue).prod) = 168067351171479637048183757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_401
      · exact prime_fiftyEightBD_20051
      · exact prime_fiftyEightBD_5225681717713335889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 168067351171479637048183757) ^ 84033675585739818524091878 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 168067351171479637048183757) ^ 419120576487480391641356 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 168067351171479637048183757) ^ 8381993475212190765956 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 168067351171479637048183757) ^ 32161804 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_175374627309370056050278703 : Nat.Prime 175374627309370056050278703 := by
  apply lucas_primality 175374627309370056050278703 (5 : ZMod 175374627309370056050278703)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (9749, 1), (802777, 1), (260563343429209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (9749, 1), (802777, 1), (260563343429209, 1)] : List FactorBlock).map factorBlockValue).prod) = 175374627309370056050278703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_43
      · exact prime_fiftyEightBD_9749
      · exact prime_fiftyEightBD_802777
      · exact prime_fiftyEightBD_260563343429209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175374627309370056050278703) ^ 87687313654685028025139351 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 175374627309370056050278703) ^ 4078479704869071070936714 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 175374627309370056050278703) ^ 17988986286734029751798 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 175374627309370056050278703) ^ 218459955017856834526 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 175374627309370056050278703) ^ 673059475678 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_230105635160951986294157627 : Nat.Prime 230105635160951986294157627 := by
  apply lucas_primality 230105635160951986294157627 (2 : ZMod 230105635160951986294157627)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1549, 1), (25189, 1), (37501, 1), (2125153681709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1549, 1), (25189, 1), (37501, 1), (2125153681709, 1)] : List FactorBlock).map factorBlockValue).prod) = 230105635160951986294157627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_37
      · exact prime_fiftyEightBD_1549
      · exact prime_fiftyEightBD_25189
      · exact prime_fiftyEightBD_37501
      · exact prime_fiftyEightBD_2125153681709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230105635160951986294157627) ^ 115052817580475993147078813 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 230105635160951986294157627) ^ 6219071220566269899842098 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 230105635160951986294157627) ^ 148551087902486756807074 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 230105635160951986294157627) ^ 9135163569850013350834 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 230105635160951986294157627) ^ 6135986644648195682626 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 230105635160951986294157627) ^ 108277174089314 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_320427473261512579045135387 : Nat.Prime 320427473261512579045135387 := by
  apply lucas_primality 320427473261512579045135387 (2 : ZMod 320427473261512579045135387)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1787, 1), (29885046937279666018013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1787, 1), (29885046937279666018013, 1)] : List FactorBlock).map factorBlockValue).prod) = 320427473261512579045135387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1787
      · exact prime_fiftyEightBD_29885046937279666018013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 320427473261512579045135387) ^ 160213736630756289522567693 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320427473261512579045135387) ^ 106809157753837526348378462 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320427473261512579045135387) ^ 179310281623677996108078 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320427473261512579045135387) ^ 10722 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_2981368664259290952854737949 : Nat.Prime 2981368664259290952854737949 := by
  apply lucas_primality 2981368664259290952854737949 (2 : ZMod 2981368664259290952854737949)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1279, 1), (52977622152592418666123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1279, 1), (52977622152592418666123, 1)] : List FactorBlock).map factorBlockValue).prod) = 2981368664259290952854737949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_1279
      · exact prime_fiftyEightBD_52977622152592418666123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2981368664259290952854737949) ^ 1490684332129645476427368974 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981368664259290952854737949) ^ 271033514932662813895885268 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981368664259290952854737949) ^ 2331015374714066421309412 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981368664259290952854737949) ^ 56276 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_3265308537045890091221855851 : Nat.Prime 3265308537045890091221855851 := by
  apply lucas_primality 3265308537045890091221855851 (13 : ZMod 3265308537045890091221855851)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (23, 1), (29, 1), (61, 1), (12211, 1), (61933, 1), (707463351319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (23, 1), (29, 1), (61, 1), (12211, 1), (61933, 1), (707463351319, 1)] : List FactorBlock).map factorBlockValue).prod) = 3265308537045890091221855851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_5
      · exact prime_fiftyEightBD_23
      · exact prime_fiftyEightBD_29
      · exact prime_fiftyEightBD_61
      · exact prime_fiftyEightBD_12211
      · exact prime_fiftyEightBD_61933
      · exact prime_fiftyEightBD_707463351319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3265308537045890091221855851) ^ 1632654268522945045610927925 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 1088436179015296697073951950 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 653061707409178018244371170 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 141969936393299569183558950 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 112596846105030692800753650 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 53529648148293280183964850 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 267407135946760305562350 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 52723241842731501642450 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3265308537045890091221855851) ^ 4615516169082150 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_6857147927796369191565897283 : Nat.Prime 6857147927796369191565897283 := by
  apply lucas_primality 6857147927796369191565897283 (2 : ZMod 6857147927796369191565897283)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (6791, 1), (25117, 1), (352644545742191579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (6791, 1), (25117, 1), (352644545742191579, 1)] : List FactorBlock).map factorBlockValue).prod) = 6857147927796369191565897283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_19
      · exact prime_fiftyEightBD_6791
      · exact prime_fiftyEightBD_25117
      · exact prime_fiftyEightBD_352644545742191579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6857147927796369191565897283) ^ 3428573963898184595782948641 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6857147927796369191565897283) ^ 2285715975932123063855299094 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6857147927796369191565897283) ^ 360902522515598378503468278 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6857147927796369191565897283) ^ 1009740528316355351430702 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6857147927796369191565897283) ^ 273008238555415423480746 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6857147927796369191565897283) ^ 19444928358 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_9795925611137670273665567557 : Nat.Prime 9795925611137670273665567557 := by
  apply lucas_primality 9795925611137670273665567557 (5 : ZMod 9795925611137670273665567557)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (71, 1), (149319029497251238852289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (71, 1), (149319029497251238852289, 1)] : List FactorBlock).map factorBlockValue).prod) = 9795925611137670273665567557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_7
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_71
      · exact prime_fiftyEightBD_149319029497251238852289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9795925611137670273665567557) ^ 4897962805568835136832783778 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9795925611137670273665567557) ^ 3265308537045890091221855852 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9795925611137670273665567557) ^ 1399417944448238610523652508 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9795925611137670273665567557) ^ 890538691921606388515051596 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9795925611137670273665567557) ^ 137970783255460144699515036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 9795925611137670273665567557) ^ 65604 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_11428579879660615319276495467 : Nat.Prime 11428579879660615319276495467 := by
  apply lucas_primality 11428579879660615319276495467 (2 : ZMod 11428579879660615319276495467)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (26437, 1), (69499, 1), (1570267, 1), (5039709361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (26437, 1), (69499, 1), (1570267, 1), (5039709361, 1)] : List FactorBlock).map factorBlockValue).prod) = 11428579879660615319276495467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_131
      · exact prime_fiftyEightBD_26437
      · exact prime_fiftyEightBD_69499
      · exact prime_fiftyEightBD_1570267
      · exact prime_fiftyEightBD_5039709361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11428579879660615319276495467) ^ 5714289939830307659638247733 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11428579879660615319276495467) ^ 3809526626553538439758831822 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11428579879660615319276495467) ^ 87241067783668819231118286 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11428579879660615319276495467) ^ 432294885185936956510818 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11428579879660615319276495467) ^ 164442364345682892117534 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11428579879660615319276495467) ^ 7278112499123152507998 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11428579879660615319276495467) ^ 2267706143552871306 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_17142869819490922978914743213 : Nat.Prime 17142869819490922978914743213 := by
  apply lucas_primality 17142869819490922978914743213 (2 : ZMod 17142869819490922978914743213)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (23346599, 1), (538326219503144617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (23346599, 1), (538326219503144617, 1)] : List FactorBlock).map factorBlockValue).prod) = 17142869819490922978914743213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_11
      · exact prime_fiftyEightBD_31
      · exact prime_fiftyEightBD_23346599
      · exact prime_fiftyEightBD_538326219503144617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17142869819490922978914743213) ^ 8571434909745461489457371606 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17142869819490922978914743213) ^ 1558442710862811179901340292 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17142869819490922978914743213) ^ 552995800628739450932733652 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17142869819490922978914743213) ^ 734276963402289257588 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17142869819490922978914743213) ^ 31844761036 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_34285739638981845957829486427 : Nat.Prime 34285739638981845957829486427 := by
  apply lucas_primality 34285739638981845957829486427 (2 : ZMod 34285739638981845957829486427)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17142869819490922978914743213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17142869819490922978914743213, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845957829486427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_17142869819490922978914743213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34285739638981845957829486427) ^ 17142869819490922978914743213 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34285739638981845957829486427) ^ 2 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem prime_fiftyEightBD_68571479277963691915658972833 : Nat.Prime 68571479277963691915658972833 := by
  apply lucas_primality 68571479277963691915658972833 (5 : ZMod 68571479277963691915658972833)
  · rw [← fiftyEightBDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (1889, 1), (39949033, 1), (1051699207826999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (1889, 1), (39949033, 1), (1051699207826999, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyEightBD_2
      · exact prime_fiftyEightBD_3
      · exact prime_fiftyEightBD_1889
      · exact prime_fiftyEightBD_39949033
      · exact prime_fiftyEightBD_1051699207826999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68571479277963691915658972833) ^ 34285739638981845957829486416 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 68571479277963691915658972833) ^ 22857159759321230638552990944 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 68571479277963691915658972833) ^ 36300412534655210119459488 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 68571479277963691915658972833) ^ 1716474070297613759904 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide
    · change (5 : ZMod 68571479277963691915658972833) ^ 65200656963168 ≠ 1
      rw [← fiftyEightBDFastPow_eq_pow]
      decide

private theorem phi_fiftyEightBD_68571479277963691915658972800 : Nat.totient 68571479277963691915658972800 = 27428591543867930466358763520 := by
  rw [← show ((([(2, 7), (5, 2), (163931353, 1), (130716832882869293, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_163931353, prime_fiftyEightBD_130716832882869293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972801 : Nat.totient 68571479277963691915658972801 = 54324003372556449796878049920 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (3282213419, 1), (3831256283251343, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_7, prime_fiftyEightBD_19, prime_fiftyEightBD_41, prime_fiftyEightBD_3282213419, prime_fiftyEightBD_3831256283251343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972802 : Nat.totient 68571479277963691915658972802 = 22857159759321230638552990932 := by
  rw [← show ((([(2, 1), (3, 1), (11428579879660615319276495467, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_11428579879660615319276495467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972803 : Nat.totient 68571479277963691915658972803 = 67248554932581150691487232000 := by
  rw [← show ((([(59, 1), (433, 1), (15401, 1), (111431, 1), (1464467, 1), (1067994637, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_59, prime_fiftyEightBD_433, prime_fiftyEightBD_15401, prime_fiftyEightBD_111431, prime_fiftyEightBD_1464467, prime_fiftyEightBD_1067994637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972804 : Nat.totient 68571479277963691915658972804 = 29790376488845768864333723040 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (1279, 1), (52977622152592418666123, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_11, prime_fiftyEightBD_23, prime_fiftyEightBD_1279, prime_fiftyEightBD_52977622152592418666123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972805 : Nat.totient 68571479277963691915658972805 = 34315739661919747482013925376 := by
  rw [← show ((([(3, 3), (5, 1), (17, 1), (479, 1), (1087, 1), (41777, 1), (196337, 1), (6996105827, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_17, prime_fiftyEightBD_479, prime_fiftyEightBD_1087, prime_fiftyEightBD_41777, prime_fiftyEightBD_196337, prime_fiftyEightBD_6996105827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972806 : Nat.totient 68571479277963691915658972806 = 33091351725719414924539577856 := by
  rw [← show ((([(2, 1), (47, 1), (73, 1), (6329, 1), (1578911213453177529197, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_47, prime_fiftyEightBD_73, prime_fiftyEightBD_6329, prime_fiftyEightBD_1578911213453177529197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972807 : Nat.totient 68571479277963691915658972807 = 65914362366834522479656554432 := by
  rw [← show ((([(37, 1), (83, 1), (22328713538900583495818617, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_37, prime_fiftyEightBD_83, prime_fiftyEightBD_22328713538900583495818617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972808 : Nat.totient 68571479277963691915658972808 = 19591851127509208858242134016 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (206738957, 1), (1974294409982615233, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_7, prime_fiftyEightBD_206738957, prime_fiftyEightBD_1974294409982615233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972809 : Nat.totient 68571479277963691915658972809 = 68570873408520446754568746000 := by
  rw [← show ((([(113363, 1), (69592751, 1), (8691769160005693, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_113363, prime_fiftyEightBD_69592751, prime_fiftyEightBD_8691769160005693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972810 : Nat.totient 68571479277963691915658972810 = 25318698059688679041568603200 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (12778151, 1), (41279283483408329587, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_13, prime_fiftyEightBD_12778151, prime_fiftyEightBD_41279283483408329587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972811 : Nat.totient 68571479277963691915658972811 = 44938017988896670671875466240 := by
  rw [← show ((([(3, 1), (67, 1), (587, 1), (3373, 1), (11719, 1), (375209, 1), (39185845091, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_67, prime_fiftyEightBD_587, prime_fiftyEightBD_3373, prime_fiftyEightBD_11719, prime_fiftyEightBD_375209, prime_fiftyEightBD_39185845091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972812 : Nat.totient 68571479277963691915658972812 = 33574270934280321430305120000 := by
  rw [← show ((([(2, 2), (79, 1), (211, 1), (331, 1), (2203, 1), (9333109, 1), (151114156651, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_79, prime_fiftyEightBD_211, prime_fiftyEightBD_331, prime_fiftyEightBD_2203, prime_fiftyEightBD_9333109, prime_fiftyEightBD_151114156651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972813 : Nat.totient 68571479277963691915658972813 = 68542299194914080436878990000 := by
  rw [← show ((([(2351, 1), (5215663, 1), (5592182895981950701, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2351, prime_fiftyEightBD_5215663, prime_fiftyEightBD_5592182895981950701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972814 : Nat.totient 68571479277963691915658972814 = 22606009478195346079363032000 := by
  rw [← show ((([(2, 1), (3, 2), (101, 1), (911, 1), (41402947762262538606893, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_101, prime_fiftyEightBD_911, prime_fiftyEightBD_41402947762262538606893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972815 : Nat.totient 68571479277963691915658972815 = 42735563165945328197640675840 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (7789, 1), (8893, 1), (2571300254725544647, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_5, prime_fiftyEightBD_7, prime_fiftyEightBD_11, prime_fiftyEightBD_7789, prime_fiftyEightBD_8893, prime_fiftyEightBD_2571300254725544647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972816 : Nat.totient 68571479277963691915658972816 = 34260925321983364653053275776 := by
  rw [← show ((([(2, 4), (2503, 1), (3083, 1), (555378625749357759949, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_2503, prime_fiftyEightBD_3083, prime_fiftyEightBD_555378625749357759949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972817 : Nat.totient 68571479277963691915658972817 = 44137019818163891211336488400 := by
  rw [← show ((([(3, 1), (31, 1), (431, 1), (1710737202254414388036299, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_31, prime_fiftyEightBD_431, prime_fiftyEightBD_1710737202254414388036299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972818 : Nat.totient 68571479277963691915658972818 = 33965312165720333378784350916 := by
  rw [← show ((([(2, 1), (107, 1), (320427473261512579045135387, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_107, prime_fiftyEightBD_320427473261512579045135387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972819 : Nat.totient 68571479277963691915658972819 = 68392441473010817465734237960 := by
  rw [← show ((([(383, 1), (1394561063723, 1), (128382908113991, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_383, prime_fiftyEightBD_1394561063723, prime_fiftyEightBD_128382908113991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972820 : Nat.totient 68571479277963691915658972820 = 17320080553846675240318824960 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19, 1), (6791, 1), (25117, 1), (352644545742191579, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_19, prime_fiftyEightBD_6791, prime_fiftyEightBD_25117, prime_fiftyEightBD_352644545742191579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972821 : Nat.totient 68571479277963691915658972821 = 64929313929090455545162936320 := by
  rw [← show ((([(29, 1), (71, 1), (227, 1), (1193, 1), (20857, 1), (5896156873742197, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_29, prime_fiftyEightBD_71, prime_fiftyEightBD_227, prime_fiftyEightBD_1193, prime_fiftyEightBD_20857, prime_fiftyEightBD_5896156873742197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972822 : Nat.totient 68571479277963691915658972822 = 27517678152503405144902041600 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (197, 1), (28621, 1), (953681, 1), (2106679, 1), (25433963, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_7, prime_fiftyEightBD_17, prime_fiftyEightBD_197, prime_fiftyEightBD_28621, prime_fiftyEightBD_953681, prime_fiftyEightBD_2106679, prime_fiftyEightBD_25433963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972823 : Nat.totient 68571479277963691915658972823 = 42153094957368530564877772800 := by
  rw [← show ((([(3, 2), (13, 1), (1373, 1), (3011, 1), (748828261, 1), (189318971993, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_13, prime_fiftyEightBD_1373, prime_fiftyEightBD_3011, prime_fiftyEightBD_748828261, prime_fiftyEightBD_189318971993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972824 : Nat.totient 68571479277963691915658972824 = 34285732193961361733857600000 := by
  rw [← show ((([(2, 3), (4643153, 1), (563356751, 1), (3276853561901, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_4643153, prime_fiftyEightBD_563356751, prime_fiftyEightBD_3276853561901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972825 : Nat.totient 68571479277963691915658972825 = 54492291541451476420716652800 := by
  rw [← show ((([(5, 2), (157, 1), (3533, 1), (992843, 1), (4980576806310011, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_5, prime_fiftyEightBD_157, prime_fiftyEightBD_3533, prime_fiftyEightBD_992843, prime_fiftyEightBD_4980576806310011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972826 : Nat.totient 68571479277963691915658972826 = 20287097825336092785341583360 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (43, 1), (4139, 1), (5077, 1), (1149816502783782209, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_11, prime_fiftyEightBD_43, prime_fiftyEightBD_4139, prime_fiftyEightBD_5077, prime_fiftyEightBD_1149816502783782209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972827 : Nat.totient 68571479277963691915658972827 = 65590110613704400962804234856 := by
  rw [← show ((([(23, 1), (2981368664259290952854737949, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_23, prime_fiftyEightBD_2981368664259290952854737949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972828 : Nat.totient 68571479277963691915658972828 = 34284792754515581166038482752 := by
  rw [← show ((([(2, 2), (36209, 1), (473442233132395895465623, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_36209, prime_fiftyEightBD_473442233132395895465623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972829 : Nat.totient 68571479277963691915658972829 = 39150982524198391107392581632 := by
  rw [← show ((([(3, 1), (7, 1), (1873, 1), (3319, 1), (676420753, 1), (776537208959, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_7, prime_fiftyEightBD_1873, prime_fiftyEightBD_3319, prime_fiftyEightBD_676420753, prime_fiftyEightBD_776537208959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972830 : Nat.totient 68571479277963691915658972830 = 27428591711185476766263589128 := by
  rw [← show ((([(2, 1), (5, 1), (6857147927796369191565897283, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_6857147927796369191565897283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972831 : Nat.totient 68571479277963691915658972831 = 68563192996832463920283245568 := by
  rw [← show ((([(8317, 1), (1650379, 1), (4995662934552754817, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_8317, prime_fiftyEightBD_1650379, prime_fiftyEightBD_4995662934552754817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972832 : Nat.totient 68571479277963691915658972832 = 22845059049954523119116304384 := by
  rw [← show ((([(2, 5), (3, 3), (1889, 1), (39949033, 1), (1051699207826999, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_1889, prime_fiftyEightBD_39949033, prime_fiftyEightBD_1051699207826999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972833 : Nat.totient 68571479277963691915658972833 = 68571479277963691915658972832 := by
  rw [← show ((([(68571479277963691915658972833, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_68571479277963691915658972833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972834 : Nat.totient 68571479277963691915658972834 = 34285553948365281299691626400 := by
  rw [← show ((([(2, 1), (186299, 1), (20722283, 1), (8881072156967401, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_186299, prime_fiftyEightBD_20722283, prime_fiftyEightBD_8881072156967401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972835 : Nat.totient 68571479277963691915658972835 = 36484154264977796513988200448 := by
  rw [← show ((([(3, 1), (5, 1), (419, 1), (2077939, 1), (33733573, 1), (155647840273, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_419, prime_fiftyEightBD_2077939, prime_fiftyEightBD_33733573, prime_fiftyEightBD_155647840273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972836 : Nat.totient 68571479277963691915658972836 = 26615345002710383135213637120 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (53, 1), (493191421, 1), (7206937433255723, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_7, prime_fiftyEightBD_13, prime_fiftyEightBD_53, prime_fiftyEightBD_493191421, prime_fiftyEightBD_7206937433255723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972837 : Nat.totient 68571479277963691915658972837 = 61882688664917465829659058400 := by
  rw [← show ((([(11, 1), (137, 1), (45501976959498136639455191, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_11, prime_fiftyEightBD_137, prime_fiftyEightBD_45501976959498136639455191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972838 : Nat.totient 68571479277963691915658972838 = 22774642931345353479068351328 := by
  rw [← show ((([(2, 1), (3, 1), (277, 1), (3967667563, 1), (10398656254031623, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_277, prime_fiftyEightBD_3967667563, prime_fiftyEightBD_10398656254031623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972839 : Nat.totient 68571479277963691915658972839 = 61140702530455407419961746304 := by
  rw [← show ((([(17, 1), (19, 1), (141959, 1), (1495471238031852521227, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_17, prime_fiftyEightBD_19, prime_fiftyEightBD_141959, prime_fiftyEightBD_1495471238031852521227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972840 : Nat.totient 68571479277963691915658972840 = 27427366719347241471462063360 := by
  rw [← show ((([(2, 3), (5, 1), (22391, 1), (3062756899, 1), (24997553723869, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_22391, prime_fiftyEightBD_3062756899, prime_fiftyEightBD_24997553723869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972841 : Nat.totient 68571479277963691915658972841 = 45714319513176887005947933984 := by
  rw [← show ((([(3, 2), (8364046973, 1), (910929036828961013, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_8364046973, prime_fiftyEightBD_910929036828961013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972842 : Nat.totient 68571479277963691915658972842 = 33186120180578737250302569600 := by
  rw [← show ((([(2, 1), (41, 1), (127, 1), (1028385073943, 1), (6402803601221, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_41, prime_fiftyEightBD_127, prime_fiftyEightBD_1028385073943, prime_fiftyEightBD_6402803601221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972843 : Nat.totient 68571479277963691915658972843 = 58775553666740056272395810688 := by
  rw [← show ((([(7, 3), (685318219357, 1), (291713898098993, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_7, prime_fiftyEightBD_685318219357, prime_fiftyEightBD_291713898098993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972844 : Nat.totient 68571479277963691915658972844 = 22191157039008007233067737600 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (461, 1), (335011428728985616441241, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_37, prime_fiftyEightBD_461, prime_fiftyEightBD_335011428728985616441241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972845 : Nat.totient 68571479277963691915658972845 = 54852186866817408496227605520 := by
  rw [← show ((([(5, 1), (10979, 1), (1249138888386259074882211, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_5, prime_fiftyEightBD_10979, prime_fiftyEightBD_1249138888386259074882211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972846 : Nat.totient 68571479277963691915658972846 = 34055634003820893971535328648 := by
  rw [← show ((([(2, 1), (149, 1), (230105635160951986294157627, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_149, prime_fiftyEightBD_230105635160951986294157627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972847 : Nat.totient 68571479277963691915658972847 = 45696413262353489459056219680 := by
  rw [← show ((([(3, 1), (2711, 1), (43783, 1), (192569379142793730373, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_2711, prime_fiftyEightBD_43783, prime_fiftyEightBD_192569379142793730373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972848 : Nat.totient 68571479277963691915658972848 = 30163406015039225005479283200 := by
  rw [← show ((([(2, 4), (11, 1), (31, 1), (23346599, 1), (538326219503144617, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_11, prime_fiftyEightBD_31, prime_fiftyEightBD_23346599, prime_fiftyEightBD_538326219503144617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972849 : Nat.totient 68571479277963691915658972849 = 61994310268718002006543564800 := by
  rw [← show ((([(13, 1), (97, 1), (163, 1), (401, 1), (563, 1), (15479029, 1), (95465037209, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_13, prime_fiftyEightBD_97, prime_fiftyEightBD_163, prime_fiftyEightBD_401, prime_fiftyEightBD_563, prime_fiftyEightBD_15479029, prime_fiftyEightBD_95465037209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972850 : Nat.totient 68571479277963691915658972850 = 14236366997206659660106752000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (7, 1), (23, 1), (29, 1), (61, 1), (12211, 1), (61933, 1), (707463351319, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_7, prime_fiftyEightBD_23, prime_fiftyEightBD_29, prime_fiftyEightBD_61, prime_fiftyEightBD_12211, prime_fiftyEightBD_61933, prime_fiftyEightBD_707463351319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972851 : Nat.totient 68571479277963691915658972851 = 68413262867508643939347467520 := by
  rw [← show ((([(443, 1), (19961, 1), (7754566017499778282737, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_443, prime_fiftyEightBD_19961, prime_fiftyEightBD_7754566017499778282737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972852 : Nat.totient 68571479277963691915658972852 = 34285739638981845957829486424 := by
  rw [← show ((([(2, 2), (17142869819490922978914743213, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_17142869819490922978914743213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972853 : Nat.totient 68571479277963691915658972853 = 44345730401063069195941222912 := by
  rw [← show ((([(3, 1), (47, 1), (113, 2), (38086189057143431879657, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_47, prime_fiftyEightBD_113, prime_fiftyEightBD_38086189057143431879657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972854 : Nat.totient 68571479277963691915658972854 = 34285739638981845957829486426 := by
  rw [← show ((([(2, 1), (34285739638981845957829486427, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_34285739638981845957829486427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972855 : Nat.totient 68571479277963691915658972855 = 54857183420964472993146278176 := by
  rw [← show ((([(5, 1), (39003162839, 1), (351620095842062189, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_5, prime_fiftyEightBD_39003162839, prime_fiftyEightBD_351620095842062189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972856 : Nat.totient 68571479277963691915658972856 = 21512620949949393542167520768 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (168067351171479637048183757, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_17, prime_fiftyEightBD_168067351171479637048183757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972857 : Nat.totient 68571479277963691915658972857 = 58435810582046680476432748752 := by
  rw [← show ((([(7, 1), (173, 1), (56623847463223527593442587, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_7, prime_fiftyEightBD_173, prime_fiftyEightBD_56623847463223527593442587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972858 : Nat.totient 68571479277963691915658972858 = 32293483776330666628496788800 := by
  rw [← show ((([(2, 1), (19, 1), (239, 1), (661, 1), (11119, 1), (1027294188385307891, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_19, prime_fiftyEightBD_239, prime_fiftyEightBD_661, prime_fiftyEightBD_11119, prime_fiftyEightBD_1027294188385307891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972859 : Nat.totient 68571479277963691915658972859 = 41411622564269752907625568560 := by
  rw [← show ((([(3, 4), (11, 1), (283, 1), (271943935935577573598803, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_11, prime_fiftyEightBD_283, prime_fiftyEightBD_271943935935577573598803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972860 : Nat.totient 68571479277963691915658972860 = 27350890318235942837747258880 := by
  rw [← show ((([(2, 2), (5, 1), (353, 1), (9712674118691741064540931, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_353, prime_fiftyEightBD_9712674118691741064540931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972861 : Nat.totient 68571479277963691915658972861 = 67735564763372932598474400000 := by
  rw [← show ((([(241, 1), (251, 1), (263, 1), (3271, 1), (1317699744834545927, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_241, prime_fiftyEightBD_251, prime_fiftyEightBD_263, prime_fiftyEightBD_3271, prime_fiftyEightBD_1317699744834545927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972862 : Nat.totient 68571479277963691915658972862 = 20741268969547794182386374144 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (59, 1), (532187, 1), (27998363172670404113, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_13, prime_fiftyEightBD_59, prime_fiftyEightBD_532187, prime_fiftyEightBD_27998363172670404113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972863 : Nat.totient 68571479277963691915658972863 = 67797765708842964299394077760 := by
  rw [← show ((([(89, 2), (20939, 1), (7148311, 1), (57836783094107, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_89, prime_fiftyEightBD_20939, prime_fiftyEightBD_7148311, prime_fiftyEightBD_57836783094107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972864 : Nat.totient 68571479277963691915658972864 = 29370041301226279975600490496 := by
  rw [← show ((([(2, 6), (7, 1), (1657, 1), (92372563472556486436949, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_7, prime_fiftyEightBD_1657, prime_fiftyEightBD_92372563472556486436949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972865 : Nat.totient 68571479277963691915658972865 = 36559861193621912930257442304 := by
  rw [← show ((([(3, 1), (5, 1), (4259, 1), (12157, 1), (88291359214560546857, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_4259, prime_fiftyEightBD_12157, prime_fiftyEightBD_88291359214560546857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972866 : Nat.totient 68571479277963691915658972866 = 34285739396736903003730594000 := by
  rw [← show ((([(2, 1), (150158711, 1), (2533200701, 1), (90134985203, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_150158711, prime_fiftyEightBD_2533200701, prime_fiftyEightBD_90134985203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972867 : Nat.totient 68571479277963691915658972867 = 67868246576378600377493344320 := by
  rw [← show ((([(167, 1), (233, 1), (761611, 1), (2313864475017799127, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_167, prime_fiftyEightBD_233, prime_fiftyEightBD_761611, prime_fiftyEightBD_2313864475017799127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972868 : Nat.totient 68571479277963691915658972868 = 22836914267948935482982957056 := by
  rw [← show ((([(2, 2), (3, 2), (1129, 1), (1687124281024596297501697, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_1129, prime_fiftyEightBD_1687124281024596297501697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972869 : Nat.totient 68571479277963691915658972869 = 66949710476958823043477985408 := by
  rw [← show ((([(43, 1), (2473, 1), (3317595317, 1), (194369240315963, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_43, prime_fiftyEightBD_2473, prime_fiftyEightBD_3317595317, prime_fiftyEightBD_194369240315963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972870 : Nat.totient 68571479277963691915658972870 = 24934531157241486774540230400 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (45161, 1), (315529223, 1), (43746941503339, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_11, prime_fiftyEightBD_45161, prime_fiftyEightBD_315529223, prime_fiftyEightBD_43746941503339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972871 : Nat.totient 68571479277963691915658972871 = 39183702444550681094662270200 := by
  rw [← show ((([(3, 1), (7, 1), (3265308537045890091221855851, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_7, prime_fiftyEightBD_3265308537045890091221855851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972872 : Nat.totient 68571479277963691915658972872 = 34277474039831637238513225728 := by
  rw [← show ((([(2, 3), (4327, 1), (116107, 1), (734017, 1), (23243531552093, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_4327, prime_fiftyEightBD_116107, prime_fiftyEightBD_734017, prime_fiftyEightBD_23243531552093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972873 : Nat.totient 68571479277963691915658972873 = 61731868812898259729698103104 := by
  rw [← show ((([(17, 1), (23, 1), (175374627309370056050278703, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_17, prime_fiftyEightBD_23, prime_fiftyEightBD_175374627309370056050278703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972874 : Nat.totient 68571479277963691915658972874 = 22641964803379870708813492032 := by
  rw [← show ((([(2, 1), (3, 1), (199, 1), (229, 1), (22123, 1), (11335996157753140663, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_199, prime_fiftyEightBD_229, prime_fiftyEightBD_22123, prime_fiftyEightBD_11335996157753140663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972875 : Nat.totient 68571479277963691915658972875 = 50637400082169126367589078400 := by
  rw [← show ((([(5, 3), (13, 1), (3259669256383, 1), (12945434055677, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_5, prime_fiftyEightBD_13, prime_fiftyEightBD_3259669256383, prime_fiftyEightBD_12945434055677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972876 : Nat.totient 68571479277963691915658972876 = 34285699157565674244576591360 := by
  rw [← show ((([(2, 2), (1350073, 1), (2523581, 1), (25910077, 1), (194196019, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_1350073, prime_fiftyEightBD_2523581, prime_fiftyEightBD_25910077, prime_fiftyEightBD_194196019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972877 : Nat.totient 68571479277963691915658972877 = 43308302701867348200610550688 := by
  rw [← show ((([(3, 2), (19, 1), (15654127509043, 1), (25616426246909, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_19, prime_fiftyEightBD_15654127509043, prime_fiftyEightBD_25616426246909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972878 : Nat.totient 68571479277963691915658972878 = 28949014462382459636265372672 := by
  rw [← show ((([(2, 1), (7, 1), (67, 1), (208513, 1), (350596473462933456587, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_7, prime_fiftyEightBD_67, prime_fiftyEightBD_208513, prime_fiftyEightBD_350596473462933456587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972879 : Nat.totient 68571479277963691915658972879 = 63186241256657436416202950400 := by
  rw [← show ((([(29, 1), (31, 3), (73, 1), (8647, 1), (125739613191606331, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_29, prime_fiftyEightBD_31, prime_fiftyEightBD_73, prime_fiftyEightBD_8647, prime_fiftyEightBD_125739613191606331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972880 : Nat.totient 68571479277963691915658972880 = 18280047369810865622151168000 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (6361, 1), (8009, 1), (37223, 1), (574711, 1), (262160771, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_6361, prime_fiftyEightBD_8009, prime_fiftyEightBD_37223, prime_fiftyEightBD_574711, prime_fiftyEightBD_262160771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972881 : Nat.totient 68571479277963691915658972881 = 60652905221900609222042390400 := by
  rw [← show ((([(11, 1), (37, 1), (215119871, 1), (783192609232504873, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_11, prime_fiftyEightBD_37, prime_fiftyEightBD_215119871, prime_fiftyEightBD_783192609232504873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972882 : Nat.totient 68571479277963691915658972882 = 34285521409394710275241831200 := by
  rw [← show ((([(2, 1), (206347, 1), (658403, 1), (252361768716178601, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_206347, prime_fiftyEightBD_658403, prime_fiftyEightBD_252361768716178601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972883 : Nat.totient 68571479277963691915658972883 = 44599334225364751440139571520 := by
  rw [← show ((([(3, 1), (41, 1), (23592739, 1), (23629799890841808739, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_41, prime_fiftyEightBD_23592739, prime_fiftyEightBD_23629799890841808739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972884 : Nat.totient 68571479277963691915658972884 = 34266445430514918082054557696 := by
  rw [← show ((([(2, 2), (1777, 1), (884963749, 1), (10901107400158177, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_1777, prime_fiftyEightBD_884963749, prime_fiftyEightBD_10901107400158177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972885 : Nat.totient 68571479277963691915658972885 = 47020442895023281234038533376 := by
  rw [← show ((([(5, 1), (7, 1), (1223294929, 1), (1601564002091546359, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_5, prime_fiftyEightBD_7, prime_fiftyEightBD_1223294929, prime_fiftyEightBD_1601564002091546359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972886 : Nat.totient 68571479277963691915658972886 = 22794864925213470150761484960 := by
  rw [← show ((([(2, 1), (3, 3), (367, 1), (1680659, 1), (126366971, 1), (16291854143, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_367, prime_fiftyEightBD_1680659, prime_fiftyEightBD_126366971, prime_fiftyEightBD_16291854143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972887 : Nat.totient 68571479277963691915658972887 = 68074927776095817789129444984 := by
  rw [← show ((([(139, 1), (21067, 1), (23416717843332899152399, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_139, prime_fiftyEightBD_21067, prime_fiftyEightBD_23416717843332899152399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972888 : Nat.totient 68571479277963691915658972888 = 31556410974309825309585859200 := by
  rw [← show ((([(2, 3), (13, 1), (347, 1), (41611, 1), (45663852802687124591, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_13, prime_fiftyEightBD_347, prime_fiftyEightBD_41611, prime_fiftyEightBD_45663852802687124591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972889 : Nat.totient 68571479277963691915658972889 = 44851783311891875159969489088 := by
  rw [← show ((([(3, 1), (53, 1), (23905523, 1), (18040482329970856477, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_53, prime_fiftyEightBD_23905523, prime_fiftyEightBD_18040482329970856477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972890 : Nat.totient 68571479277963691915658972890 = 25504119290588532992648448000 := by
  rw [← show ((([(2, 1), (5, 1), (17, 2), (83, 1), (5944046747, 1), (48093387393001, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_17, prime_fiftyEightBD_83, prime_fiftyEightBD_5944046747, prime_fiftyEightBD_48093387393001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972891 : Nat.totient 68571479277963691915658972891 = 67082278236200547237177316992 := by
  rw [← show ((([(79, 1), (109, 1), (904999, 1), (109929467, 1), (80043801757, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_79, prime_fiftyEightBD_109, prime_fiftyEightBD_904999, prime_fiftyEightBD_109929467, prime_fiftyEightBD_80043801757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972892 : Nat.totient 68571479277963691915658972892 = 17559917868876745689029068800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (11, 1), (71, 1), (149319029497251238852289, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_7, prime_fiftyEightBD_11, prime_fiftyEightBD_71, prime_fiftyEightBD_149319029497251238852289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972893 : Nat.totient 68571479277963691915658972893 = 68571375210386822186738235520 := by
  rw [← show ((([(658913, 1), (104067576869728920078461, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_658913, prime_fiftyEightBD_104067576869728920078461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972894 : Nat.totient 68571479277963691915658972894 = 34285730786219272572591114624 := by
  rw [← show ((([(2, 1), (3873209, 1), (80009037529, 1), (110637803327, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3873209, prime_fiftyEightBD_80009037529, prime_fiftyEightBD_110637803327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972895 : Nat.totient 68571479277963691915658972895 = 36535353486962425123341538368 := by
  rw [← show ((([(3, 2), (5, 1), (1013, 1), (1504255331314329097634287, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_3, prime_fiftyEightBD_5, prime_fiftyEightBD_1013, prime_fiftyEightBD_1504255331314329097634287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972896 : Nat.totient 68571479277963691915658972896 = 30766619008886848849568378880 := by
  rw [← show ((([(2, 5), (19, 1), (23, 1), (103, 1), (41609, 1), (57022331, 1), (20065160287, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_19, prime_fiftyEightBD_23, prime_fiftyEightBD_103, prime_fiftyEightBD_41609, prime_fiftyEightBD_57022331, prime_fiftyEightBD_20065160287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972897 : Nat.totient 68571479277963691915658972897 = 68470192011642493295408738800 := by
  rw [← show ((([(677, 1), (2266667347391, 1), (44685545237171, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_677, prime_fiftyEightBD_2266667347391, prime_fiftyEightBD_44685545237171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972898 : Nat.totient 68571479277963691915658972898 = 22790839981052710744367984640 := by
  rw [← show ((([(2, 1), (3, 1), (379, 1), (7547, 1), (9173, 1), (45121, 1), (9653584412327, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_3, prime_fiftyEightBD_379, prime_fiftyEightBD_7547, prime_fiftyEightBD_9173, prime_fiftyEightBD_45121, prime_fiftyEightBD_9653584412327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972899 : Nat.totient 68571479277963691915658972899 = 58775553666826021641993405336 := by
  rw [← show ((([(7, 1), (9795925611137670273665567557, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_7, prime_fiftyEightBD_9795925611137670273665567557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyEightBD_68571479277963691915658972900 : Nat.totient 68571479277963691915658972900 = 26843933979682089643092067840 := by
  rw [← show ((([(2, 2), (5, 2), (47, 1), (25073, 1), (581887944885731043359, 1)] : List FactorBlock).map factorBlockValue).prod) = 68571479277963691915658972900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyEightBD_2, prime_fiftyEightBD_5, prime_fiftyEightBD_47, prime_fiftyEightBD_25073, prime_fiftyEightBD_581887944885731043359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyEightBD : certifiedKill 1 68571479277963691915658972799 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyEightBD_68571479277963691915658972800, phi_fiftyEightBD_68571479277963691915658972801, phi_fiftyEightBD_68571479277963691915658972802,
    phi_fiftyEightBD_68571479277963691915658972803, phi_fiftyEightBD_68571479277963691915658972804, phi_fiftyEightBD_68571479277963691915658972805,
    phi_fiftyEightBD_68571479277963691915658972806, phi_fiftyEightBD_68571479277963691915658972807, phi_fiftyEightBD_68571479277963691915658972808,
    phi_fiftyEightBD_68571479277963691915658972809, phi_fiftyEightBD_68571479277963691915658972810, phi_fiftyEightBD_68571479277963691915658972811,
    phi_fiftyEightBD_68571479277963691915658972812, phi_fiftyEightBD_68571479277963691915658972813, phi_fiftyEightBD_68571479277963691915658972814,
    phi_fiftyEightBD_68571479277963691915658972815, phi_fiftyEightBD_68571479277963691915658972816, phi_fiftyEightBD_68571479277963691915658972817,
    phi_fiftyEightBD_68571479277963691915658972818, phi_fiftyEightBD_68571479277963691915658972819, phi_fiftyEightBD_68571479277963691915658972820,
    phi_fiftyEightBD_68571479277963691915658972821, phi_fiftyEightBD_68571479277963691915658972822, phi_fiftyEightBD_68571479277963691915658972823,
    phi_fiftyEightBD_68571479277963691915658972824, phi_fiftyEightBD_68571479277963691915658972825, phi_fiftyEightBD_68571479277963691915658972826,
    phi_fiftyEightBD_68571479277963691915658972827, phi_fiftyEightBD_68571479277963691915658972828, phi_fiftyEightBD_68571479277963691915658972829,
    phi_fiftyEightBD_68571479277963691915658972830, phi_fiftyEightBD_68571479277963691915658972831, phi_fiftyEightBD_68571479277963691915658972832,
    phi_fiftyEightBD_68571479277963691915658972833, phi_fiftyEightBD_68571479277963691915658972834, phi_fiftyEightBD_68571479277963691915658972835,
    phi_fiftyEightBD_68571479277963691915658972836, phi_fiftyEightBD_68571479277963691915658972837, phi_fiftyEightBD_68571479277963691915658972838,
    phi_fiftyEightBD_68571479277963691915658972839, phi_fiftyEightBD_68571479277963691915658972840, phi_fiftyEightBD_68571479277963691915658972841,
    phi_fiftyEightBD_68571479277963691915658972842, phi_fiftyEightBD_68571479277963691915658972843, phi_fiftyEightBD_68571479277963691915658972844,
    phi_fiftyEightBD_68571479277963691915658972845, phi_fiftyEightBD_68571479277963691915658972846, phi_fiftyEightBD_68571479277963691915658972847,
    phi_fiftyEightBD_68571479277963691915658972848, phi_fiftyEightBD_68571479277963691915658972849, phi_fiftyEightBD_68571479277963691915658972850,
    phi_fiftyEightBD_68571479277963691915658972851, phi_fiftyEightBD_68571479277963691915658972852, phi_fiftyEightBD_68571479277963691915658972853,
    phi_fiftyEightBD_68571479277963691915658972854, phi_fiftyEightBD_68571479277963691915658972855, phi_fiftyEightBD_68571479277963691915658972856,
    phi_fiftyEightBD_68571479277963691915658972857, phi_fiftyEightBD_68571479277963691915658972858, phi_fiftyEightBD_68571479277963691915658972859,
    phi_fiftyEightBD_68571479277963691915658972860, phi_fiftyEightBD_68571479277963691915658972861, phi_fiftyEightBD_68571479277963691915658972862,
    phi_fiftyEightBD_68571479277963691915658972863, phi_fiftyEightBD_68571479277963691915658972864, phi_fiftyEightBD_68571479277963691915658972865,
    phi_fiftyEightBD_68571479277963691915658972866, phi_fiftyEightBD_68571479277963691915658972867, phi_fiftyEightBD_68571479277963691915658972868,
    phi_fiftyEightBD_68571479277963691915658972869, phi_fiftyEightBD_68571479277963691915658972870, phi_fiftyEightBD_68571479277963691915658972871,
    phi_fiftyEightBD_68571479277963691915658972872, phi_fiftyEightBD_68571479277963691915658972873, phi_fiftyEightBD_68571479277963691915658972874,
    phi_fiftyEightBD_68571479277963691915658972875, phi_fiftyEightBD_68571479277963691915658972876, phi_fiftyEightBD_68571479277963691915658972877,
    phi_fiftyEightBD_68571479277963691915658972878, phi_fiftyEightBD_68571479277963691915658972879, phi_fiftyEightBD_68571479277963691915658972880,
    phi_fiftyEightBD_68571479277963691915658972881, phi_fiftyEightBD_68571479277963691915658972882, phi_fiftyEightBD_68571479277963691915658972883,
    phi_fiftyEightBD_68571479277963691915658972884, phi_fiftyEightBD_68571479277963691915658972885, phi_fiftyEightBD_68571479277963691915658972886,
    phi_fiftyEightBD_68571479277963691915658972887, phi_fiftyEightBD_68571479277963691915658972888, phi_fiftyEightBD_68571479277963691915658972889,
    phi_fiftyEightBD_68571479277963691915658972890, phi_fiftyEightBD_68571479277963691915658972891, phi_fiftyEightBD_68571479277963691915658972892,
    phi_fiftyEightBD_68571479277963691915658972893, phi_fiftyEightBD_68571479277963691915658972894, phi_fiftyEightBD_68571479277963691915658972895,
    phi_fiftyEightBD_68571479277963691915658972896, phi_fiftyEightBD_68571479277963691915658972897, phi_fiftyEightBD_68571479277963691915658972898,
    phi_fiftyEightBD_68571479277963691915658972899, phi_fiftyEightBD_68571479277963691915658972900]

end TotientTailPeriodKiller
end Erdos249257
