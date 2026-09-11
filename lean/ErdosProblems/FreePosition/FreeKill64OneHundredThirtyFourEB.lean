import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyFourEBFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyFourEBFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyFourEBFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyFourEBFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyFourEBFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyFourEBFastPow a n * oneHundredThirtyFourEBFastPow a n * a else oneHundredThirtyFourEBFastPow a n * oneHundredThirtyFourEBFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyFourEB_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyFourEB_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyFourEB_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyFourEB_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyFourEB_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyFourEB_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyFourEB_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyFourEB_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyFourEB_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyFourEB_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyFourEB_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyFourEB_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyFourEB_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyFourEB_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyFourEB_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyFourEB_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyFourEB_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyFourEB_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyFourEB_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyFourEB_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyFourEB_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyFourEB_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyFourEB_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyFourEB_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyFourEB_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyFourEB_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyFourEB_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyFourEB_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyFourEB_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyFourEB_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyFourEB_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtyFourEB_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyFourEB_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtyFourEB_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyFourEB_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyFourEB_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyFourEB_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyFourEB_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirtyFourEB_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyFourEB_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtyFourEB_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyFourEB_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtyFourEB_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyFourEB_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtyFourEB_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirtyFourEB_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtyFourEB_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyFourEB_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtyFourEB_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtyFourEB_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtyFourEB_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtyFourEB_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtyFourEB_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyFourEB_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirtyFourEB_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtyFourEB_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredThirtyFourEB_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtyFourEB_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredThirtyFourEB_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtyFourEB_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThirtyFourEB_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredThirtyFourEB_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtyFourEB_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtyFourEB_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirtyFourEB_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirtyFourEB_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirtyFourEB_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtyFourEB_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirtyFourEB_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredThirtyFourEB_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtyFourEB_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredThirtyFourEB_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtyFourEB_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredThirtyFourEB_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirtyFourEB_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredThirtyFourEB_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirtyFourEB_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredThirtyFourEB_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyFourEB_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtyFourEB_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredThirtyFourEB_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredThirtyFourEB_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirtyFourEB_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredThirtyFourEB_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredThirtyFourEB_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThirtyFourEB_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirtyFourEB_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredThirtyFourEB_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredThirtyFourEB_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtyFourEB_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredThirtyFourEB_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtyFourEB_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredThirtyFourEB_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredThirtyFourEB_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredThirtyFourEB_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredThirtyFourEB_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredThirtyFourEB_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredThirtyFourEB_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredThirtyFourEB_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredThirtyFourEB_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredThirtyFourEB_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredThirtyFourEB_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredThirtyFourEB_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThirtyFourEB_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredThirtyFourEB_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredThirtyFourEB_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirtyFourEB_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredThirtyFourEB_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredThirtyFourEB_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2557 : Nat.Prime 2557 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3329 : Nat.Prime 3329 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4099 : Nat.Prime 4099 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4751 : Nat.Prime 4751 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4789 : Nat.Prime 4789 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4799 : Nat.Prime 4799 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5099 : Nat.Prime 5099 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5107 : Nat.Prime 5107 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5261 : Nat.Prime 5261 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5279 : Nat.Prime 5279 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5591 : Nat.Prime 5591 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5683 : Nat.Prime 5683 := by norm_num

private theorem prime_oneHundredThirtyFourEB_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6221 : Nat.Prime 6221 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6359 : Nat.Prime 6359 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6581 : Nat.Prime 6581 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6733 : Nat.Prime 6733 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6781 : Nat.Prime 6781 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6833 : Nat.Prime 6833 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6917 : Nat.Prime 6917 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7019 : Nat.Prime 7019 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7219 : Nat.Prime 7219 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7309 : Nat.Prime 7309 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7883 : Nat.Prime 7883 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7907 : Nat.Prime 7907 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_oneHundredThirtyFourEB_8017 : Nat.Prime 8017 := by norm_num

private theorem prime_oneHundredThirtyFourEB_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_oneHundredThirtyFourEB_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredThirtyFourEB_8419 : Nat.Prime 8419 := by norm_num

private theorem prime_oneHundredThirtyFourEB_8753 : Nat.Prime 8753 := by norm_num

private theorem prime_oneHundredThirtyFourEB_9949 : Nat.Prime 9949 := by norm_num

private theorem prime_oneHundredThirtyFourEB_10433 : Nat.Prime 10433 := by norm_num

private theorem prime_oneHundredThirtyFourEB_11171 : Nat.Prime 11171 := by norm_num

private theorem prime_oneHundredThirtyFourEB_11213 : Nat.Prime 11213 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12161 : Nat.Prime 12161 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12281 : Nat.Prime 12281 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12809 : Nat.Prime 12809 := by norm_num

private theorem prime_oneHundredThirtyFourEB_14639 : Nat.Prime 14639 := by norm_num

private theorem prime_oneHundredThirtyFourEB_15271 : Nat.Prime 15271 := by norm_num

private theorem prime_oneHundredThirtyFourEB_15551 : Nat.Prime 15551 := by norm_num

private theorem prime_oneHundredThirtyFourEB_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredThirtyFourEB_16421 : Nat.Prime 16421 := by norm_num

private theorem prime_oneHundredThirtyFourEB_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyFourEB_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredThirtyFourEB_18199 : Nat.Prime 18199 := by norm_num

private theorem prime_oneHundredThirtyFourEB_18583 : Nat.Prime 18583 := by norm_num

private theorem prime_oneHundredThirtyFourEB_19597 : Nat.Prime 19597 := by norm_num

private theorem prime_oneHundredThirtyFourEB_19801 : Nat.Prime 19801 := by norm_num

private theorem prime_oneHundredThirtyFourEB_20549 : Nat.Prime 20549 := by norm_num

private theorem prime_oneHundredThirtyFourEB_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyFourEB_21157 : Nat.Prime 21157 := by norm_num

private theorem prime_oneHundredThirtyFourEB_21419 : Nat.Prime 21419 := by norm_num

private theorem prime_oneHundredThirtyFourEB_21601 : Nat.Prime 21601 := by norm_num

private theorem prime_oneHundredThirtyFourEB_21817 : Nat.Prime 21817 := by norm_num

private theorem prime_oneHundredThirtyFourEB_22409 : Nat.Prime 22409 := by norm_num

private theorem prime_oneHundredThirtyFourEB_23339 : Nat.Prime 23339 := by norm_num

private theorem prime_oneHundredThirtyFourEB_23509 : Nat.Prime 23509 := by norm_num

private theorem prime_oneHundredThirtyFourEB_23629 : Nat.Prime 23629 := by norm_num

private theorem prime_oneHundredThirtyFourEB_24859 : Nat.Prime 24859 := by norm_num

private theorem prime_oneHundredThirtyFourEB_24977 : Nat.Prime 24977 := by norm_num

private theorem prime_oneHundredThirtyFourEB_25357 : Nat.Prime 25357 := by norm_num

private theorem prime_oneHundredThirtyFourEB_25541 : Nat.Prime 25541 := by norm_num

private theorem prime_oneHundredThirtyFourEB_25997 : Nat.Prime 25997 := by norm_num

private theorem prime_oneHundredThirtyFourEB_26821 : Nat.Prime 26821 := by norm_num

private theorem prime_oneHundredThirtyFourEB_27073 : Nat.Prime 27073 := by norm_num

private theorem prime_oneHundredThirtyFourEB_28663 : Nat.Prime 28663 := by norm_num

private theorem prime_oneHundredThirtyFourEB_29201 : Nat.Prime 29201 := by norm_num

private theorem prime_oneHundredThirtyFourEB_29629 : Nat.Prime 29629 := by norm_num

private theorem prime_oneHundredThirtyFourEB_29947 : Nat.Prime 29947 := by norm_num

private theorem prime_oneHundredThirtyFourEB_30013 : Nat.Prime 30013 := by norm_num

private theorem prime_oneHundredThirtyFourEB_30293 : Nat.Prime 30293 := by norm_num

private theorem prime_oneHundredThirtyFourEB_31139 : Nat.Prime 31139 := by norm_num

private theorem prime_oneHundredThirtyFourEB_31991 : Nat.Prime 31991 := by norm_num

private theorem prime_oneHundredThirtyFourEB_32603 : Nat.Prime 32603 := by norm_num

private theorem prime_oneHundredThirtyFourEB_32971 : Nat.Prime 32971 := by norm_num

private theorem prime_oneHundredThirtyFourEB_33053 : Nat.Prime 33053 := by norm_num

private theorem prime_oneHundredThirtyFourEB_33329 : Nat.Prime 33329 := by norm_num

private theorem prime_oneHundredThirtyFourEB_35393 : Nat.Prime 35393 := by norm_num

private theorem prime_oneHundredThirtyFourEB_35603 : Nat.Prime 35603 := by norm_num

private theorem prime_oneHundredThirtyFourEB_38669 : Nat.Prime 38669 := by norm_num

private theorem prime_oneHundredThirtyFourEB_42043 : Nat.Prime 42043 := by norm_num

private theorem prime_oneHundredThirtyFourEB_42073 : Nat.Prime 42073 := by norm_num

private theorem prime_oneHundredThirtyFourEB_42089 : Nat.Prime 42089 := by norm_num

private theorem prime_oneHundredThirtyFourEB_42989 : Nat.Prime 42989 := by norm_num

private theorem prime_oneHundredThirtyFourEB_43573 : Nat.Prime 43573 := by norm_num

private theorem prime_oneHundredThirtyFourEB_44701 : Nat.Prime 44701 := by norm_num

private theorem prime_oneHundredThirtyFourEB_46061 : Nat.Prime 46061 := by norm_num

private theorem prime_oneHundredThirtyFourEB_47741 : Nat.Prime 47741 := by norm_num

private theorem prime_oneHundredThirtyFourEB_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredThirtyFourEB_49871 : Nat.Prime 49871 := by norm_num

private theorem prime_oneHundredThirtyFourEB_53861 : Nat.Prime 53861 := by norm_num

private theorem prime_oneHundredThirtyFourEB_54413 : Nat.Prime 54413 := by norm_num

private theorem prime_oneHundredThirtyFourEB_57793 : Nat.Prime 57793 := by norm_num

private theorem prime_oneHundredThirtyFourEB_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredThirtyFourEB_71399 : Nat.Prime 71399 := by norm_num

private theorem prime_oneHundredThirtyFourEB_72977 : Nat.Prime 72977 := by norm_num

private theorem prime_oneHundredThirtyFourEB_73939 : Nat.Prime 73939 := by norm_num

private theorem prime_oneHundredThirtyFourEB_79397 : Nat.Prime 79397 := by norm_num

private theorem prime_oneHundredThirtyFourEB_83869 : Nat.Prime 83869 := by norm_num

private theorem prime_oneHundredThirtyFourEB_85411 : Nat.Prime 85411 := by norm_num

private theorem prime_oneHundredThirtyFourEB_87187 : Nat.Prime 87187 := by norm_num

private theorem prime_oneHundredThirtyFourEB_91513 : Nat.Prime 91513 := by norm_num

private theorem prime_oneHundredThirtyFourEB_94819 : Nat.Prime 94819 := by norm_num

private theorem prime_oneHundredThirtyFourEB_94847 : Nat.Prime 94847 := by norm_num

private theorem prime_oneHundredThirtyFourEB_101111 : Nat.Prime 101111 := by norm_num

private theorem prime_oneHundredThirtyFourEB_102071 : Nat.Prime 102071 := by norm_num

private theorem prime_oneHundredThirtyFourEB_105031 : Nat.Prime 105031 := by norm_num

private theorem prime_oneHundredThirtyFourEB_110729 : Nat.Prime 110729 := by norm_num

private theorem prime_oneHundredThirtyFourEB_117053 : Nat.Prime 117053 := by norm_num

private theorem prime_oneHundredThirtyFourEB_123637 : Nat.Prime 123637 := by norm_num

private theorem prime_oneHundredThirtyFourEB_123953 : Nat.Prime 123953 := by norm_num

private theorem prime_oneHundredThirtyFourEB_125339 : Nat.Prime 125339 := by norm_num

private theorem prime_oneHundredThirtyFourEB_127241 : Nat.Prime 127241 := by norm_num

private theorem prime_oneHundredThirtyFourEB_132523 : Nat.Prime 132523 := by norm_num

private theorem prime_oneHundredThirtyFourEB_134191 : Nat.Prime 134191 := by norm_num

private theorem prime_oneHundredThirtyFourEB_135623 : Nat.Prime 135623 := by norm_num

private theorem prime_oneHundredThirtyFourEB_138401 : Nat.Prime 138401 := by norm_num

private theorem prime_oneHundredThirtyFourEB_144031 : Nat.Prime 144031 := by norm_num

private theorem prime_oneHundredThirtyFourEB_160313 : Nat.Prime 160313 := by norm_num

private theorem prime_oneHundredThirtyFourEB_161611 : Nat.Prime 161611 := by norm_num

private theorem prime_oneHundredThirtyFourEB_170579 : Nat.Prime 170579 := by norm_num

private theorem prime_oneHundredThirtyFourEB_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyFourEB_171811 : Nat.Prime 171811 := by norm_num

private theorem prime_oneHundredThirtyFourEB_178793 : Nat.Prime 178793 := by norm_num

private theorem prime_oneHundredThirtyFourEB_180001 : Nat.Prime 180001 := by norm_num

private theorem prime_oneHundredThirtyFourEB_194899 : Nat.Prime 194899 := by norm_num

private theorem prime_oneHundredThirtyFourEB_196831 : Nat.Prime 196831 := by norm_num

private theorem prime_oneHundredThirtyFourEB_200003 : Nat.Prime 200003 := by norm_num

private theorem prime_oneHundredThirtyFourEB_200171 : Nat.Prime 200171 := by norm_num

private theorem prime_oneHundredThirtyFourEB_206191 : Nat.Prime 206191 := by norm_num

private theorem prime_oneHundredThirtyFourEB_247991 : Nat.Prime 247991 := by norm_num

private theorem prime_oneHundredThirtyFourEB_252017 : Nat.Prime 252017 := by norm_num

private theorem prime_oneHundredThirtyFourEB_290659 : Nat.Prime 290659 := by norm_num

private theorem prime_oneHundredThirtyFourEB_294551 : Nat.Prime 294551 := by norm_num

private theorem prime_oneHundredThirtyFourEB_294659 : Nat.Prime 294659 := by norm_num

private theorem prime_oneHundredThirtyFourEB_295901 : Nat.Prime 295901 := by norm_num

private theorem prime_oneHundredThirtyFourEB_306529 : Nat.Prime 306529 := by norm_num

private theorem prime_oneHundredThirtyFourEB_307277 : Nat.Prime 307277 := by norm_num

private theorem prime_oneHundredThirtyFourEB_325849 : Nat.Prime 325849 := by norm_num

private theorem prime_oneHundredThirtyFourEB_327473 : Nat.Prime 327473 := by norm_num

private theorem prime_oneHundredThirtyFourEB_328243 : Nat.Prime 328243 := by norm_num

private theorem prime_oneHundredThirtyFourEB_331697 : Nat.Prime 331697 := by norm_num

private theorem prime_oneHundredThirtyFourEB_339679 : Nat.Prime 339679 := by norm_num

private theorem prime_oneHundredThirtyFourEB_340859 : Nat.Prime 340859 := by norm_num

private theorem prime_oneHundredThirtyFourEB_361003 : Nat.Prime 361003 := by norm_num

private theorem prime_oneHundredThirtyFourEB_361549 : Nat.Prime 361549 := by norm_num

private theorem prime_oneHundredThirtyFourEB_362429 : Nat.Prime 362429 := by norm_num

private theorem prime_oneHundredThirtyFourEB_371939 : Nat.Prime 371939 := by norm_num

private theorem prime_oneHundredThirtyFourEB_374531 : Nat.Prime 374531 := by norm_num

private theorem prime_oneHundredThirtyFourEB_385573 : Nat.Prime 385573 := by norm_num

private theorem prime_oneHundredThirtyFourEB_399527 : Nat.Prime 399527 := by norm_num

private theorem prime_oneHundredThirtyFourEB_415013 : Nat.Prime 415013 := by norm_num

private theorem prime_oneHundredThirtyFourEB_420521 : Nat.Prime 420521 := by norm_num

private theorem prime_oneHundredThirtyFourEB_424147 : Nat.Prime 424147 := by norm_num

private theorem prime_oneHundredThirtyFourEB_426077 : Nat.Prime 426077 := by norm_num

private theorem prime_oneHundredThirtyFourEB_478427 : Nat.Prime 478427 := by norm_num

private theorem prime_oneHundredThirtyFourEB_506381 : Nat.Prime 506381 := by norm_num

private theorem prime_oneHundredThirtyFourEB_519581 : Nat.Prime 519581 := by norm_num

private theorem prime_oneHundredThirtyFourEB_523459 : Nat.Prime 523459 := by norm_num

private theorem prime_oneHundredThirtyFourEB_526531 : Nat.Prime 526531 := by norm_num

private theorem prime_oneHundredThirtyFourEB_536561 : Nat.Prime 536561 := by norm_num

private theorem prime_oneHundredThirtyFourEB_569417 : Nat.Prime 569417 := by norm_num

private theorem prime_oneHundredThirtyFourEB_572909 : Nat.Prime 572909 := by norm_num

private theorem prime_oneHundredThirtyFourEB_579829 : Nat.Prime 579829 := by norm_num

private theorem prime_oneHundredThirtyFourEB_592939 : Nat.Prime 592939 := by norm_num

private theorem prime_oneHundredThirtyFourEB_625489 : Nat.Prime 625489 := by norm_num

private theorem prime_oneHundredThirtyFourEB_676037 : Nat.Prime 676037 := by norm_num

private theorem prime_oneHundredThirtyFourEB_716453 : Nat.Prime 716453 := by norm_num

private theorem prime_oneHundredThirtyFourEB_716869 : Nat.Prime 716869 := by norm_num

private theorem prime_oneHundredThirtyFourEB_759581 : Nat.Prime 759581 := by norm_num

private theorem prime_oneHundredThirtyFourEB_767489 : Nat.Prime 767489 := by norm_num

private theorem prime_oneHundredThirtyFourEB_769247 : Nat.Prime 769247 := by norm_num

private theorem prime_oneHundredThirtyFourEB_771143 : Nat.Prime 771143 := by norm_num

private theorem prime_oneHundredThirtyFourEB_818399 : Nat.Prime 818399 := by norm_num

private theorem prime_oneHundredThirtyFourEB_867253 : Nat.Prime 867253 := by norm_num

private theorem prime_oneHundredThirtyFourEB_903269 : Nat.Prime 903269 := by norm_num

private theorem prime_oneHundredThirtyFourEB_941153 : Nat.Prime 941153 := by norm_num

private theorem prime_oneHundredThirtyFourEB_947861 : Nat.Prime 947861 := by norm_num

private theorem prime_oneHundredThirtyFourEB_964219 : Nat.Prime 964219 := by norm_num

private theorem prime_oneHundredThirtyFourEB_973367 : Nat.Prime 973367 := by norm_num

private theorem prime_oneHundredThirtyFourEB_996811 : Nat.Prime 996811 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1014779 : Nat.Prime 1014779 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1017361 : Nat.Prime 1017361 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1030441 : Nat.Prime 1030441 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1045859 : Nat.Prime 1045859 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1079033 : Nat.Prime 1079033 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1180807 : Nat.Prime 1180807 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1202437 : Nat.Prime 1202437 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1218953 : Nat.Prime 1218953 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1311307 : Nat.Prime 1311307 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1334393 : Nat.Prime 1334393 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1360591 : Nat.Prime 1360591 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1500991 : Nat.Prime 1500991 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1631051 : Nat.Prime 1631051 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1749383 : Nat.Prime 1749383 := by norm_num

private theorem prime_oneHundredThirtyFourEB_1915933 : Nat.Prime 1915933 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2009243 : Nat.Prime 2009243 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2122123 : Nat.Prime 2122123 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2139499 : Nat.Prime 2139499 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2205803 : Nat.Prime 2205803 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2238809 : Nat.Prime 2238809 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2302169 : Nat.Prime 2302169 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2391523 : Nat.Prime 2391523 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2535413 : Nat.Prime 2535413 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2809567 : Nat.Prime 2809567 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2883851 : Nat.Prime 2883851 := by norm_num

private theorem prime_oneHundredThirtyFourEB_2985881 : Nat.Prime 2985881 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3074633 : Nat.Prime 3074633 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3087223 : Nat.Prime 3087223 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3095977 : Nat.Prime 3095977 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3135017 : Nat.Prime 3135017 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3144419 : Nat.Prime 3144419 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3236711 : Nat.Prime 3236711 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3588457 : Nat.Prime 3588457 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3629039 : Nat.Prime 3629039 := by norm_num

private theorem prime_oneHundredThirtyFourEB_3709939 : Nat.Prime 3709939 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4217623 : Nat.Prime 4217623 := by norm_num

private theorem prime_oneHundredThirtyFourEB_4363213 : Nat.Prime 4363213 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6474623 : Nat.Prime 6474623 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6519017 : Nat.Prime 6519017 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6611807 : Nat.Prime 6611807 := by norm_num

private theorem prime_oneHundredThirtyFourEB_6696083 : Nat.Prime 6696083 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7532029 : Nat.Prime 7532029 := by norm_num

private theorem prime_oneHundredThirtyFourEB_7978709 : Nat.Prime 7978709 := by norm_num

private theorem prime_oneHundredThirtyFourEB_8044931 : Nat.Prime 8044931 := by norm_num

private theorem prime_oneHundredThirtyFourEB_9467537 : Nat.Prime 9467537 := by norm_num

private theorem prime_oneHundredThirtyFourEB_10359553 : Nat.Prime 10359553 := by norm_num

private theorem prime_oneHundredThirtyFourEB_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyFourEB_11052823 : Nat.Prime 11052823 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12010951 : Nat.Prime 12010951 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12054659 : Nat.Prime 12054659 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12374749 : Nat.Prime 12374749 := by norm_num

private theorem prime_oneHundredThirtyFourEB_12805921 : Nat.Prime 12805921 := by norm_num

private theorem prime_oneHundredThirtyFourEB_13124971 : Nat.Prime 13124971 := by norm_num

private theorem prime_oneHundredThirtyFourEB_13978633 : Nat.Prime 13978633 := by norm_num

private theorem prime_oneHundredThirtyFourEB_14438527 : Nat.Prime 14438527 := by norm_num

private theorem prime_oneHundredThirtyFourEB_14724097 : Nat.Prime 14724097 := by norm_num

private theorem prime_oneHundredThirtyFourEB_14977829 : Nat.Prime 14977829 := by norm_num

private theorem prime_oneHundredThirtyFourEB_15059311 : Nat.Prime 15059311 := by norm_num

private theorem prime_oneHundredThirtyFourEB_16866029 : Nat.Prime 16866029 := by norm_num

private theorem prime_oneHundredThirtyFourEB_17290487 : Nat.Prime 17290487 := by norm_num

private theorem prime_oneHundredThirtyFourEB_17872879 : Nat.Prime 17872879 := by norm_num

private theorem prime_oneHundredThirtyFourEB_18212741 : Nat.Prime 18212741 := by norm_num

private theorem prime_oneHundredThirtyFourEB_18306731 : Nat.Prime 18306731 := by norm_num

private theorem prime_oneHundredThirtyFourEB_19049669 : Nat.Prime 19049669 := by norm_num

private theorem prime_oneHundredThirtyFourEB_19162813 : Nat.Prime 19162813 := by norm_num

private theorem prime_oneHundredThirtyFourEB_19951433 : Nat.Prime 19951433 := by norm_num

private theorem prime_oneHundredThirtyFourEB_21033941 : Nat.Prime 21033941 := by norm_num

private theorem prime_oneHundredThirtyFourEB_21218929 : Nat.Prime 21218929 := by norm_num

private theorem prime_oneHundredThirtyFourEB_22397587 : Nat.Prime 22397587 := by norm_num

private theorem prime_oneHundredThirtyFourEB_27536189 : Nat.Prime 27536189 := by norm_num

private theorem prime_oneHundredThirtyFourEB_31746553 : Nat.Prime 31746553 := by
  apply lucas_primality 31746553 (5 : ZMod 31746553)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1031, 1), (1283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1031, 1), (1283, 1)] : List FactorBlock).map factorBlockValue).prod) = 31746553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1031
      · exact prime_oneHundredThirtyFourEB_1283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31746553) ^ 15873276 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 31746553) ^ 10582184 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 31746553) ^ 30792 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 31746553) ^ 24744 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_36895597 : Nat.Prime 36895597 := by
  apply lucas_primality 36895597 (2 : ZMod 36895597)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3074633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3074633, 1)] : List FactorBlock).map factorBlockValue).prod) = 36895597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_3074633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36895597) ^ 18447798 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 36895597) ^ 12298532 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 36895597) ^ 12 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_37303601 : Nat.Prime 37303601 := by
  apply lucas_primality 37303601 (6 : ZMod 37303601)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (179, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (179, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 37303601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_179
      · exact prime_oneHundredThirtyFourEB_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 37303601) ^ 18651800 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 37303601) ^ 7460720 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 37303601) ^ 208400 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 37303601) ^ 71600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_44297207 : Nat.Prime 44297207 := by
  apply lucas_primality 44297207 (5 : ZMod 44297207)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (163, 1), (7993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (163, 1), (7993, 1)] : List FactorBlock).map factorBlockValue).prod) = 44297207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_163
      · exact prime_oneHundredThirtyFourEB_7993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44297207) ^ 22148603 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 44297207) ^ 2605718 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 44297207) ^ 271762 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 44297207) ^ 5542 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_46802383 : Nat.Prime 46802383 := by
  apply lucas_primality 46802383 (3 : ZMod 46802383)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (173, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (173, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) = 46802383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_173
      · exact prime_oneHundredThirtyFourEB_4099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46802383) ^ 23401191 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46802383) ^ 15600794 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46802383) ^ 4254762 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46802383) ^ 270534 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46802383) ^ 11418 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_49821451 : Nat.Prime 49821451 := by
  apply lucas_primality 49821451 (3 : ZMod 49821451)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (23, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (23, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) = 49821451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49821451) ^ 24910725 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49821451) ^ 16607150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49821451) ^ 9964290 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49821451) ^ 7117350 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49821451) ^ 2166150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49821451) ^ 24150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_51207931 : Nat.Prime 51207931 := by
  apply lucas_primality 51207931 (2 : ZMod 51207931)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (89, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (89, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 51207931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_89
      · exact prime_oneHundredThirtyFourEB_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51207931) ^ 25603965 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 51207931) ^ 17069310 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 51207931) ^ 10241586 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 51207931) ^ 575370 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 51207931) ^ 24030 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_52464809 : Nat.Prime 52464809 := by
  apply lucas_primality 52464809 (3 : ZMod 52464809)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (73, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (73, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) = 52464809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_73
      · exact prime_oneHundredThirtyFourEB_8167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52464809) ^ 26232404 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52464809) ^ 4769528 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52464809) ^ 718696 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52464809) ^ 6424 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_53757983 : Nat.Prime 53757983 := by
  apply lucas_primality 53757983 (5 : ZMod 53757983)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (487, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (487, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 53757983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_97
      · exact prime_oneHundredThirtyFourEB_487
      · exact prime_oneHundredThirtyFourEB_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53757983) ^ 26878991 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53757983) ^ 554206 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53757983) ^ 110386 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53757983) ^ 94478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_55914533 : Nat.Prime 55914533 := by
  apply lucas_primality 55914533 (2 : ZMod 55914533)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13978633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13978633, 1)] : List FactorBlock).map factorBlockValue).prod) = 55914533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_13978633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 55914533) ^ 27957266 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55914533) ^ 4 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_57768077 : Nat.Prime 57768077 := by
  apply lucas_primality 57768077 (2 : ZMod 57768077)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (307277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (307277, 1)] : List FactorBlock).map factorBlockValue).prod) = 57768077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_307277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57768077) ^ 28884038 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57768077) ^ 1229108 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57768077) ^ 188 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_58896389 : Nat.Prime 58896389 := by
  apply lucas_primality 58896389 (2 : ZMod 58896389)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14724097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14724097, 1)] : List FactorBlock).map factorBlockValue).prod) = 58896389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_14724097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 58896389) ^ 29448194 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 58896389) ^ 4 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1811
      · exact prime_oneHundredThirtyFourEB_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_63576901 : Nat.Prime 63576901 := by
  apply lucas_primality 63576901 (2 : ZMod 63576901)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 2), (47, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 2), (47, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 63576901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63576901) ^ 31788450 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63576901) ^ 21192300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63576901) ^ 12715380 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63576901) ^ 1352700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63576901) ^ 380700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_63651503 : Nat.Prime 63651503 := by
  apply lucas_primality 63651503 (5 : ZMod 63651503)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (683, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (683, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 63651503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_683
      · exact prime_oneHundredThirtyFourEB_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63651503) ^ 31825751 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 63651503) ^ 3744206 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 63651503) ^ 93194 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 63651503) ^ 23222 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_65374219 : Nat.Prime 65374219 := by
  apply lucas_primality 65374219 (3 : ZMod 65374219)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (107, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (107, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 65374219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_107
      · exact prime_oneHundredThirtyFourEB_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65374219) ^ 32687109 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 65374219) ^ 21791406 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 65374219) ^ 9339174 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 65374219) ^ 5028786 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 65374219) ^ 610974 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 65374219) ^ 175266 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_69283439 : Nat.Prime 69283439 := by
  apply lucas_primality 69283439 (7 : ZMod 69283439)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (139, 1), (35603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (139, 1), (35603, 1)] : List FactorBlock).map factorBlockValue).prod) = 69283439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_139
      · exact prime_oneHundredThirtyFourEB_35603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 69283439) ^ 34641719 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69283439) ^ 9897634 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69283439) ^ 498442 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69283439) ^ 1946 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_69488921 : Nat.Prime 69488921 := by
  apply lucas_primality 69488921 (3 : ZMod 69488921)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (991, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (991, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) = 69488921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_991
      · exact prime_oneHundredThirtyFourEB_1753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 69488921) ^ 34744460 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 69488921) ^ 13897784 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 69488921) ^ 70120 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 69488921) ^ 39640 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_73853107 : Nat.Prime 73853107 := by
  apply lucas_primality 73853107 (5 : ZMod 73853107)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (599, 1), (20549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (599, 1), (20549, 1)] : List FactorBlock).map factorBlockValue).prod) = 73853107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_599
      · exact prime_oneHundredThirtyFourEB_20549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 73853107) ^ 36926553 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 73853107) ^ 24617702 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 73853107) ^ 123294 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 73853107) ^ 3594 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_75068507 : Nat.Prime 75068507 := by
  apply lucas_primality 75068507 (2 : ZMod 75068507)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (173, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (173, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) = 75068507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_173
      · exact prime_oneHundredThirtyFourEB_601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75068507) ^ 37534253 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75068507) ^ 3950974 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75068507) ^ 433922 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 75068507) ^ 124906 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_75740297 : Nat.Prime 75740297 := by
  apply lucas_primality 75740297 (3 : ZMod 75740297)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9467537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9467537, 1)] : List FactorBlock).map factorBlockValue).prod) = 75740297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_9467537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 75740297) ^ 37870148 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 75740297) ^ 8 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_75859237 : Nat.Prime 75859237 := by
  apply lucas_primality 75859237 (5 : ZMod 75859237)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (123953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (123953, 1)] : List FactorBlock).map factorBlockValue).prod) = 75859237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_123953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75859237) ^ 37929618 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 75859237) ^ 25286412 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 75859237) ^ 4462308 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 75859237) ^ 612 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_84776639 : Nat.Prime 84776639 := by
  apply lucas_primality 84776639 (19 : ZMod 84776639)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (536561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (536561, 1)] : List FactorBlock).map factorBlockValue).prod) = 84776639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_79
      · exact prime_oneHundredThirtyFourEB_536561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 84776639) ^ 42388319 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 84776639) ^ 1073122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 84776639) ^ 158 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_86116861 : Nat.Prime 86116861 := by
  apply lucas_primality 86116861 (2 : ZMod 86116861)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (478427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (478427, 1)] : List FactorBlock).map factorBlockValue).prod) = 86116861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_478427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 86116861) ^ 43058430 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 86116861) ^ 28705620 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 86116861) ^ 17223372 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 86116861) ^ 180 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_87407267 : Nat.Prime 87407267 := by
  apply lucas_primality 87407267 (2 : ZMod 87407267)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (716453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (716453, 1)] : List FactorBlock).map factorBlockValue).prod) = 87407267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_61
      · exact prime_oneHundredThirtyFourEB_716453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87407267) ^ 43703633 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 87407267) ^ 1432906 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 87407267) ^ 122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_87500977 : Nat.Prime 87500977 := by
  apply lucas_primality 87500977 (10 : ZMod 87500977)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (277, 1), (6581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (277, 1), (6581, 1)] : List FactorBlock).map factorBlockValue).prod) = 87500977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_277
      · exact prime_oneHundredThirtyFourEB_6581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 87500977) ^ 43750488 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 87500977) ^ 29166992 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 87500977) ^ 315888 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 87500977) ^ 13296 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_100718249 : Nat.Prime 100718249 := by
  apply lucas_primality 100718249 (3 : ZMod 100718249)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1993, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1993, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 100718249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1993
      · exact prime_oneHundredThirtyFourEB_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 100718249) ^ 50359124 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100718249) ^ 50536 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 100718249) ^ 15944 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_103044101 : Nat.Prime 103044101 := by
  apply lucas_primality 103044101 (2 : ZMod 103044101)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (1030441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (1030441, 1)] : List FactorBlock).map factorBlockValue).prod) = 103044101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_1030441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103044101) ^ 51522050 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 103044101) ^ 20608820 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 103044101) ^ 100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_111012947 : Nat.Prime 111012947 := by
  apply lucas_primality 111012947 (2 : ZMod 111012947)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (199, 1), (25357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (199, 1), (25357, 1)] : List FactorBlock).map factorBlockValue).prod) = 111012947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_199
      · exact prime_oneHundredThirtyFourEB_25357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111012947) ^ 55506473 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 111012947) ^ 10092086 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 111012947) ^ 557854 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 111012947) ^ 4378 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_152655731 : Nat.Prime 152655731 := by
  apply lucas_primality 152655731 (2 : ZMod 152655731)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (463, 1), (32971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (463, 1), (32971, 1)] : List FactorBlock).map factorBlockValue).prod) = 152655731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_463
      · exact prime_oneHundredThirtyFourEB_32971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152655731) ^ 76327865 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 152655731) ^ 30531146 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 152655731) ^ 329710 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 152655731) ^ 4630 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_161986459 : Nat.Prime 161986459 := by
  apply lucas_primality 161986459 (2 : ZMod 161986459)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (151, 1), (178793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (151, 1), (178793, 1)] : List FactorBlock).map factorBlockValue).prod) = 161986459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_151
      · exact prime_oneHundredThirtyFourEB_178793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 161986459) ^ 80993229 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 161986459) ^ 53995486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 161986459) ^ 1072758 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 161986459) ^ 906 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_162588421 : Nat.Prime 162588421 := by
  apply lucas_primality 162588421 (2 : ZMod 162588421)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (903269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (903269, 1)] : List FactorBlock).map factorBlockValue).prod) = 162588421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_903269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 162588421) ^ 81294210 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162588421) ^ 54196140 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162588421) ^ 32517684 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162588421) ^ 180 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_173984411 : Nat.Prime 173984411 := by
  apply lucas_primality 173984411 (2 : ZMod 173984411)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (607, 1), (28663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (607, 1), (28663, 1)] : List FactorBlock).map factorBlockValue).prod) = 173984411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_607
      · exact prime_oneHundredThirtyFourEB_28663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 173984411) ^ 86992205 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 173984411) ^ 34796882 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 173984411) ^ 286630 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 173984411) ^ 6070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_191489017 : Nat.Prime 191489017 := by
  apply lucas_primality 191489017 (10 : ZMod 191489017)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7978709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7978709, 1)] : List FactorBlock).map factorBlockValue).prod) = 191489017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7978709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 191489017) ^ 95744508 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 191489017) ^ 63829672 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 191489017) ^ 24 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_194772239 : Nat.Prime 194772239 := by
  apply lucas_primality 194772239 (7 : ZMod 194772239)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (964219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (964219, 1)] : List FactorBlock).map factorBlockValue).prod) = 194772239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_101
      · exact prime_oneHundredThirtyFourEB_964219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 194772239) ^ 97386119 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 194772239) ^ 1928438 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 194772239) ^ 202 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_223253089 : Nat.Prime 223253089 := by
  apply lucas_primality 223253089 (7 : ZMod 223253089)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (101111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (101111, 1)] : List FactorBlock).map factorBlockValue).prod) = 223253089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_101111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 223253089) ^ 111626544 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 223253089) ^ 74417696 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 223253089) ^ 9706656 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 223253089) ^ 2208 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_223594403 : Nat.Prime 223594403 := by
  apply lucas_primality 223594403 (2 : ZMod 223594403)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (61, 1), (44701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (61, 1), (44701, 1)] : List FactorBlock).map factorBlockValue).prod) = 223594403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_61
      · exact prime_oneHundredThirtyFourEB_44701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 223594403) ^ 111797201 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 223594403) ^ 5453522 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 223594403) ^ 3665482 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 223594403) ^ 5002 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_229440329 : Nat.Prime 229440329 := by
  apply lucas_primality 229440329 (3 : ZMod 229440329)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (103, 1), (21419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (103, 1), (21419, 1)] : List FactorBlock).map factorBlockValue).prod) = 229440329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_103
      · exact prime_oneHundredThirtyFourEB_21419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 229440329) ^ 114720164 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 229440329) ^ 17649256 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 229440329) ^ 2227576 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 229440329) ^ 10712 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_241537567 : Nat.Prime 241537567 := by
  apply lucas_primality 241537567 (3 : ZMod 241537567)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (415013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (415013, 1)] : List FactorBlock).map factorBlockValue).prod) = 241537567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_97
      · exact prime_oneHundredThirtyFourEB_415013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 241537567) ^ 120768783 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 241537567) ^ 80512522 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 241537567) ^ 2490078 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 241537567) ^ 582 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_251748353 : Nat.Prime 251748353 := by
  apply lucas_primality 251748353 (3 : ZMod 251748353)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 13), (79, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 13), (79, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 251748353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_79
      · exact prime_oneHundredThirtyFourEB_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 251748353) ^ 125874176 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 251748353) ^ 3186688 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 251748353) ^ 647168 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_252348641 : Nat.Prime 252348641 := by
  apply lucas_primality 252348641 (3 : ZMod 252348641)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (23, 1), (47, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (23, 1), (47, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 252348641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 252348641) ^ 126174320 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 252348641) ^ 50469728 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 252348641) ^ 10971680 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 252348641) ^ 5369120 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 252348641) ^ 172960 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_297814103 : Nat.Prime 297814103 := by
  apply lucas_primality 297814103 (5 : ZMod 297814103)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (2809567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (2809567, 1)] : List FactorBlock).map factorBlockValue).prod) = 297814103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_53
      · exact prime_oneHundredThirtyFourEB_2809567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 297814103) ^ 148907051 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 297814103) ^ 5619134 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 297814103) ^ 106 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_299556581 : Nat.Prime 299556581 := by
  apply lucas_primality 299556581 (10 : ZMod 299556581)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (14977829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (14977829, 1)] : List FactorBlock).map factorBlockValue).prod) = 299556581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_14977829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 299556581) ^ 149778290 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 299556581) ^ 59911316 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 299556581) ^ 20 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_304781783 : Nat.Prime 304781783 := by
  apply lucas_primality 304781783 (5 : ZMod 304781783)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1283, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1283, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) = 304781783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_1283
      · exact prime_oneHundredThirtyFourEB_2897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 304781783) ^ 152390891 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 304781783) ^ 7433702 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 304781783) ^ 237554 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 304781783) ^ 105206 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_327019577 : Nat.Prime 327019577 := by
  apply lucas_primality 327019577 (3 : ZMod 327019577)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (3144419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (3144419, 1)] : List FactorBlock).map factorBlockValue).prod) = 327019577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_3144419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 327019577) ^ 163509788 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 327019577) ^ 25155352 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 327019577) ^ 104 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_341503597 : Nat.Prime 341503597 := by
  apply lucas_primality 341503597 (2 : ZMod 341503597)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (41, 1), (33053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (41, 1), (33053, 1)] : List FactorBlock).map factorBlockValue).prod) = 341503597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_33053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 341503597) ^ 170751798 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 341503597) ^ 113834532 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 341503597) ^ 48786228 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 341503597) ^ 8329356 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 341503597) ^ 10332 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_347968823 : Nat.Prime 347968823 := by
  apply lucas_primality 347968823 (5 : ZMod 347968823)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173984411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173984411, 1)] : List FactorBlock).map factorBlockValue).prod) = 347968823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_173984411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 347968823) ^ 173984411 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 347968823) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_353181869 : Nat.Prime 353181869 := by
  apply lucas_primality 353181869 (7 : ZMod 353181869)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (399527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (399527, 1)] : List FactorBlock).map factorBlockValue).prod) = 353181869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_399527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 353181869) ^ 176590934 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 353181869) ^ 27167836 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 353181869) ^ 20775404 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 353181869) ^ 884 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_381960919 : Nat.Prime 381960919 := by
  apply lucas_primality 381960919 (3 : ZMod 381960919)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (487, 1), (43573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (487, 1), (43573, 1)] : List FactorBlock).map factorBlockValue).prod) = 381960919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_487
      · exact prime_oneHundredThirtyFourEB_43573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 381960919) ^ 190980459 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 381960919) ^ 127320306 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 381960919) ^ 784314 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 381960919) ^ 8766 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_386876431 : Nat.Prime 386876431 := by
  apply lucas_primality 386876431 (3 : ZMod 386876431)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (79, 1), (54413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (79, 1), (54413, 1)] : List FactorBlock).map factorBlockValue).prod) = 386876431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_79
      · exact prime_oneHundredThirtyFourEB_54413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 386876431) ^ 193438215 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 386876431) ^ 128958810 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 386876431) ^ 77375286 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 386876431) ^ 4897170 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 386876431) ^ 7110 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_442112921 : Nat.Prime 442112921 := by
  apply lucas_primality 442112921 (3 : ZMod 442112921)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11052823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11052823, 1)] : List FactorBlock).map factorBlockValue).prod) = 442112921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_11052823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 442112921) ^ 221056460 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442112921) ^ 88422584 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 442112921) ^ 40 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_453019439 : Nat.Prime 453019439 := by
  apply lucas_primality 453019439 (11 : ZMod 453019439)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (769, 1), (294551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (769, 1), (294551, 1)] : List FactorBlock).map factorBlockValue).prod) = 453019439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_769
      · exact prime_oneHundredThirtyFourEB_294551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 453019439) ^ 226509719 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 453019439) ^ 589102 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 453019439) ^ 1538 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_463743211 : Nat.Prime 463743211 := by
  apply lucas_primality 463743211 (3 : ZMod 463743211)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (53861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (53861, 1)] : List FactorBlock).map factorBlockValue).prod) = 463743211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_53861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 463743211) ^ 231871605 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 463743211) ^ 154581070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 463743211) ^ 92748642 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 463743211) ^ 66249030 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 463743211) ^ 11310810 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 463743211) ^ 8610 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_484450147 : Nat.Prime 484450147 := by
  apply lucas_primality 484450147 (3 : ZMod 484450147)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (996811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (996811, 1)] : List FactorBlock).map factorBlockValue).prod) = 484450147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_996811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 484450147) ^ 242225073 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 484450147) ^ 161483382 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 484450147) ^ 486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_491876449 : Nat.Prime 491876449 := by
  apply lucas_primality 491876449 (57 : ZMod 491876449)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (211, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (211, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 491876449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_211
      · exact prime_oneHundredThirtyFourEB_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (57 : ZMod 491876449) ^ 245938224 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (57 : ZMod 491876449) ^ 163958816 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (57 : ZMod 491876449) ^ 70268064 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (57 : ZMod 491876449) ^ 2331168 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (57 : ZMod 491876449) ^ 141792 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_513937777 : Nat.Prime 513937777 := by
  apply lucas_primality 513937777 (7 : ZMod 513937777)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (973367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (973367, 1)] : List FactorBlock).map factorBlockValue).prod) = 513937777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_973367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 513937777) ^ 256968888 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 513937777) ^ 171312592 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 513937777) ^ 46721616 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 513937777) ^ 528 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_594130013 : Nat.Prime 594130013 := by
  apply lucas_primality 594130013 (2 : ZMod 594130013)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (21218929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (21218929, 1)] : List FactorBlock).map factorBlockValue).prod) = 594130013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_21218929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 594130013) ^ 297065006 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 594130013) ^ 84875716 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 594130013) ^ 28 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_614495173 : Nat.Prime 614495173 := by
  apply lucas_primality 614495173 (2 : ZMod 614495173)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (51207931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (51207931, 1)] : List FactorBlock).map factorBlockValue).prod) = 614495173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_51207931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 614495173) ^ 307247586 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614495173) ^ 204831724 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614495173) ^ 12 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_640293211 : Nat.Prime 640293211 := by
  apply lucas_primality 640293211 (2 : ZMod 640293211)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (61, 1), (223, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (61, 1), (223, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 640293211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_61
      · exact prime_oneHundredThirtyFourEB_223
      · exact prime_oneHundredThirtyFourEB_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640293211) ^ 320146605 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640293211) ^ 213431070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640293211) ^ 128058642 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640293211) ^ 10496610 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640293211) ^ 2871270 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640293211) ^ 1224270 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_661988693 : Nat.Prime 661988693 := by
  apply lucas_primality 661988693 (2 : ZMod 661988693)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3593, 1), (46061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3593, 1), (46061, 1)] : List FactorBlock).map factorBlockValue).prod) = 661988693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3593
      · exact prime_oneHundredThirtyFourEB_46061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 661988693) ^ 330994346 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 661988693) ^ 184244 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 661988693) ^ 14372 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_706363739 : Nat.Prime 706363739 := by
  apply lucas_primality 706363739 (2 : ZMod 706363739)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (353181869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (353181869, 1)] : List FactorBlock).map factorBlockValue).prod) = 706363739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_353181869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 706363739) ^ 353181869 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 706363739) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17203
      · exact prime_oneHundredThirtyFourEB_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_746574683 : Nat.Prime 746574683 := by
  apply lucas_primality 746574683 (2 : ZMod 746574683)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (181, 1), (42089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (181, 1), (42089, 1)] : List FactorBlock).map factorBlockValue).prod) = 746574683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_181
      · exact prime_oneHundredThirtyFourEB_42089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 746574683) ^ 373287341 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746574683) ^ 106653526 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746574683) ^ 4124722 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 746574683) ^ 17738 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_878723089 : Nat.Prime 878723089 := by
  apply lucas_primality 878723089 (7 : ZMod 878723089)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (18306731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (18306731, 1)] : List FactorBlock).map factorBlockValue).prod) = 878723089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_18306731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 878723089) ^ 439361544 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 878723089) ^ 292907696 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 878723089) ^ 48 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_920695147 : Nat.Prime 920695147 := by
  apply lucas_primality 920695147 (2 : ZMod 920695147)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (263, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (263, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) = 920695147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_263
      · exact prime_oneHundredThirtyFourEB_4903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 920695147) ^ 460347573 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 920695147) ^ 306898382 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 920695147) ^ 131527878 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 920695147) ^ 54158538 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 920695147) ^ 3500742 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 920695147) ^ 187782 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_961392247 : Nat.Prime 961392247 := by
  apply lucas_primality 961392247 (5 : ZMod 961392247)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (2391523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (2391523, 1)] : List FactorBlock).map factorBlockValue).prod) = 961392247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_67
      · exact prime_oneHundredThirtyFourEB_2391523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 961392247) ^ 480696123 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 961392247) ^ 320464082 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 961392247) ^ 14349138 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 961392247) ^ 402 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1010148583 : Nat.Prime 1010148583 := by
  apply lucas_primality 1010148583 (5 : ZMod 1010148583)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1931, 1), (87187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1931, 1), (87187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1010148583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1931
      · exact prime_oneHundredThirtyFourEB_87187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1010148583) ^ 505074291 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010148583) ^ 336716194 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010148583) ^ 523122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010148583) ^ 11586 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1020522539 : Nat.Prime 1020522539 := by
  apply lucas_primality 1020522539 (2 : ZMod 1020522539)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (227, 1), (317, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (227, 1), (317, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1020522539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_227
      · exact prime_oneHundredThirtyFourEB_317
      · exact prime_oneHundredThirtyFourEB_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1020522539) ^ 510261269 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1020522539) ^ 145788934 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1020522539) ^ 4495694 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1020522539) ^ 3219314 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1020522539) ^ 1007426 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1085077171 : Nat.Prime 1085077171 := by
  apply lucas_primality 1085077171 (2 : ZMod 1085077171)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (325849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (325849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085077171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_37
      · exact prime_oneHundredThirtyFourEB_325849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1085077171) ^ 542538585 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085077171) ^ 361692390 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085077171) ^ 217015434 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085077171) ^ 29326410 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085077171) ^ 3330 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1120897861 : Nat.Prime 1120897861 := by
  apply lucas_primality 1120897861 (6 : ZMod 1120897861)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (883, 1), (21157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (883, 1), (21157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1120897861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_883
      · exact prime_oneHundredThirtyFourEB_21157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1120897861) ^ 560448930 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1120897861) ^ 373632620 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1120897861) ^ 224179572 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1120897861) ^ 1269420 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1120897861) ^ 52980 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1140486337 : Nat.Prime 1140486337 := by
  apply lucas_primality 1140486337 (5 : ZMod 1140486337)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 1), (180001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 1), (180001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140486337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_180001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1140486337) ^ 570243168 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140486337) ^ 380162112 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140486337) ^ 103680576 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140486337) ^ 6336 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1190451389 : Nat.Prime 1190451389 := by
  apply lucas_primality 1190451389 (2 : ZMod 1190451389)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (43, 1), (42989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (43, 1), (42989, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190451389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_42989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1190451389) ^ 595225694 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190451389) ^ 170064484 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190451389) ^ 51758756 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190451389) ^ 27684916 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1190451389) ^ 27692 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1224682483 : Nat.Prime 1224682483 := by
  apply lucas_primality 1224682483 (3 : ZMod 1224682483)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (61, 1), (196831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (61, 1), (196831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1224682483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_61
      · exact prime_oneHundredThirtyFourEB_196831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1224682483) ^ 612341241 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1224682483) ^ 408227494 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1224682483) ^ 72040146 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1224682483) ^ 20076762 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1224682483) ^ 6222 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1236529213 : Nat.Prime 1236529213 := by
  apply lucas_primality 1236529213 (5 : ZMod 1236529213)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (103044101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (103044101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1236529213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_103044101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1236529213) ^ 618264606 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1236529213) ^ 412176404 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1236529213) ^ 12 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1297637543 : Nat.Prime 1297637543 := by
  apply lucas_primality 1297637543 (5 : ZMod 1297637543)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3329, 1), (194899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3329, 1), (194899, 1)] : List FactorBlock).map factorBlockValue).prod) = 1297637543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3329
      · exact prime_oneHundredThirtyFourEB_194899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1297637543) ^ 648818771 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1297637543) ^ 389798 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1297637543) ^ 6658 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1342363213 : Nat.Prime 1342363213 := by
  apply lucas_primality 1342363213 (2 : ZMod 1342363213)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (97, 2), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (97, 2), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342363213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_97
      · exact prime_oneHundredThirtyFourEB_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1342363213) ^ 671181606 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342363213) ^ 447454404 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342363213) ^ 13838796 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342363213) ^ 1016172 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1343195081 : Nat.Prime 1343195081 := by
  apply lucas_primality 1343195081 (3 : ZMod 1343195081)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (193, 1), (257, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (193, 1), (257, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343195081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_193
      · exact prime_oneHundredThirtyFourEB_257
      · exact prime_oneHundredThirtyFourEB_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1343195081) ^ 671597540 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343195081) ^ 268639016 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343195081) ^ 6959560 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343195081) ^ 5226440 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343195081) ^ 1984040 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1377204239 : Nat.Prime 1377204239 := by
  apply lucas_primality 1377204239 (11 : ZMod 1377204239)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1723, 1), (23509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1723, 1), (23509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1377204239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_1723
      · exact prime_oneHundredThirtyFourEB_23509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1377204239) ^ 688602119 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1377204239) ^ 81012014 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1377204239) ^ 799306 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1377204239) ^ 58582 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1386433849 : Nat.Prime 1386433849 := by
  apply lucas_primality 1386433849 (7 : ZMod 1386433849)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (57768077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (57768077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1386433849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_57768077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1386433849) ^ 693216924 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1386433849) ^ 462144616 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1386433849) ^ 24 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1411103081 : Nat.Prime 1411103081 := by
  apply lucas_primality 1411103081 (3 : ZMod 1411103081)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (67, 1), (526531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (67, 1), (526531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1411103081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_67
      · exact prime_oneHundredThirtyFourEB_526531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1411103081) ^ 705551540 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411103081) ^ 282220616 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411103081) ^ 21061240 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411103081) ^ 2680 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1493149367 : Nat.Prime 1493149367 := by
  apply lucas_primality 1493149367 (5 : ZMod 1493149367)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (746574683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (746574683, 1)] : List FactorBlock).map factorBlockValue).prod) = 1493149367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_746574683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1493149367) ^ 746574683 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1493149367) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1501370141 : Nat.Prime 1501370141 := by
  apply lucas_primality 1501370141 (2 : ZMod 1501370141)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (75068507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (75068507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1501370141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_75068507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1501370141) ^ 750685070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501370141) ^ 300274028 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501370141) ^ 20 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1504784231 : Nat.Prime 1504784231 := by
  apply lucas_primality 1504784231 (11 : ZMod 1504784231)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (1667, 1), (4751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (1667, 1), (4751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1504784231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_1667
      · exact prime_oneHundredThirtyFourEB_4751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1504784231) ^ 752392115 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1504784231) ^ 300956846 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1504784231) ^ 79199170 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1504784231) ^ 902690 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1504784231) ^ 316730 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1514443753 : Nat.Prime 1514443753 := by
  apply lucas_primality 1514443753 (15 : ZMod 1514443753)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (21033941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (21033941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514443753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_21033941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 1514443753) ^ 757221876 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (15 : ZMod 1514443753) ^ 504814584 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (15 : ZMod 1514443753) ^ 72 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1668809221 : Nat.Prime 1668809221 := by
  apply lucas_primality 1668809221 (11 : ZMod 1668809221)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (2139499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (2139499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1668809221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_2139499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1668809221) ^ 834404610 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1668809221) ^ 556269740 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1668809221) ^ 333761844 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1668809221) ^ 128369940 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1668809221) ^ 780 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1712354939 : Nat.Prime 1712354939 := by
  apply lucas_primality 1712354939 (2 : ZMod 1712354939)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (4217623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (4217623, 1)] : List FactorBlock).map factorBlockValue).prod) = 1712354939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_4217623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1712354939) ^ 856177469 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1712354939) ^ 244622134 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1712354939) ^ 59046722 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1712354939) ^ 406 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1770402511 : Nat.Prime 1770402511 := by
  apply lucas_primality 1770402511 (3 : ZMod 1770402511)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (193, 1), (227, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (193, 1), (227, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1770402511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_193
      · exact prime_oneHundredThirtyFourEB_227
      · exact prime_oneHundredThirtyFourEB_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1770402511) ^ 885201255 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770402511) ^ 590134170 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770402511) ^ 354080502 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770402511) ^ 9173070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770402511) ^ 7799130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770402511) ^ 3942990 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2029805747 : Nat.Prime 2029805747 := by
  apply lucas_primality 2029805747 (2 : ZMod 2029805747)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1033, 1), (57793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1033, 1), (57793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2029805747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_1033
      · exact prime_oneHundredThirtyFourEB_57793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2029805747) ^ 1014902873 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2029805747) ^ 119400338 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2029805747) ^ 1964962 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2029805747) ^ 35122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2386822483 : Nat.Prime 2386822483 := by
  apply lucas_primality 2386822483 (2 : ZMod 2386822483)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (12054659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (12054659, 1)] : List FactorBlock).map factorBlockValue).prod) = 2386822483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_12054659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2386822483) ^ 1193411241 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386822483) ^ 795607494 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386822483) ^ 216983862 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386822483) ^ 198 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2992786561 : Nat.Prime 2992786561 := by
  apply lucas_primality 2992786561 (22 : ZMod 2992786561)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (519581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (519581, 1)] : List FactorBlock).map factorBlockValue).prod) = 2992786561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_519581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 2992786561) ^ 1496393280 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (22 : ZMod 2992786561) ^ 997595520 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (22 : ZMod 2992786561) ^ 598557312 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (22 : ZMod 2992786561) ^ 5760 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3002740283 : Nat.Prime 3002740283 := by
  apply lucas_primality 3002740283 (2 : ZMod 3002740283)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1501370141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1501370141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3002740283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1501370141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3002740283) ^ 1501370141 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3002740283) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3246084137 : Nat.Prime 3246084137 := by
  apply lucas_primality 3246084137 (3 : ZMod 3246084137)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5683, 1), (71399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5683, 1), (71399, 1)] : List FactorBlock).map factorBlockValue).prod) = 3246084137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5683
      · exact prime_oneHundredThirtyFourEB_71399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3246084137) ^ 1623042068 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3246084137) ^ 571192 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3246084137) ^ 45464 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3472651057 : Nat.Prime 3472651057 := by
  apply lucas_primality 3472651057 (13 : ZMod 3472651057)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (109, 1), (94819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (109, 1), (94819, 1)] : List FactorBlock).map factorBlockValue).prod) = 3472651057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_109
      · exact prime_oneHundredThirtyFourEB_94819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3472651057) ^ 1736325528 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 3472651057) ^ 1157550352 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 3472651057) ^ 496093008 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 3472651057) ^ 31859184 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 3472651057) ^ 36624 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3536903369 : Nat.Prime 3536903369 := by
  apply lucas_primality 3536903369 (3 : ZMod 3536903369)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (442112921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (442112921, 1)] : List FactorBlock).map factorBlockValue).prod) = 3536903369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_442112921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3536903369) ^ 1768451684 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3536903369) ^ 8 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3615429029 : Nat.Prime 3615429029 := by
  apply lucas_primality 3615429029 (2 : ZMod 3615429029)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2131, 1), (424147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2131, 1), (424147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3615429029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_2131
      · exact prime_oneHundredThirtyFourEB_424147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3615429029) ^ 1807714514 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3615429029) ^ 1696588 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3615429029) ^ 8524 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3779389903 : Nat.Prime 3779389903 := by
  apply lucas_primality 3779389903 (3 : ZMod 3779389903)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (101, 1), (328243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (101, 1), (328243, 1)] : List FactorBlock).map factorBlockValue).prod) = 3779389903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_101
      · exact prime_oneHundredThirtyFourEB_328243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3779389903) ^ 1889694951 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3779389903) ^ 1259796634 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3779389903) ^ 198915258 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3779389903) ^ 37419702 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3779389903) ^ 11514 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4079498713 : Nat.Prime 4079498713 := by
  apply lucas_primality 4079498713 (5 : ZMod 4079498713)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 2), (167, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 2), (167, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 4079498713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_73
      · exact prime_oneHundredThirtyFourEB_167
      · exact prime_oneHundredThirtyFourEB_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4079498713) ^ 2039749356 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4079498713) ^ 1359832904 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4079498713) ^ 55883544 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4079498713) ^ 24428136 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4079498713) ^ 21358632 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4587912853 : Nat.Prime 4587912853 := by
  apply lucas_primality 4587912853 (2 : ZMod 4587912853)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (1360591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (1360591, 1)] : List FactorBlock).map factorBlockValue).prod) = 4587912853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_281
      · exact prime_oneHundredThirtyFourEB_1360591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4587912853) ^ 2293956426 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4587912853) ^ 1529304284 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4587912853) ^ 16327092 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4587912853) ^ 3372 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_5132985757 : Nat.Prime 5132985757 := by
  apply lucas_primality 5132985757 (14 : ZMod 5132985757)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17207, 1), (24859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17207, 1), (24859, 1)] : List FactorBlock).map factorBlockValue).prod) = 5132985757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_17207
      · exact prime_oneHundredThirtyFourEB_24859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 5132985757) ^ 2566492878 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 5132985757) ^ 1710995252 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 5132985757) ^ 298308 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 5132985757) ^ 206484 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6005480567 : Nat.Prime 6005480567 := by
  apply lucas_primality 6005480567 (5 : ZMod 6005480567)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3002740283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3002740283, 1)] : List FactorBlock).map factorBlockValue).prod) = 6005480567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3002740283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6005480567) ^ 3002740283 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6005480567) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6251086493 : Nat.Prime 6251086493 := by
  apply lucas_primality 6251086493 (2 : ZMod 6251086493)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (223253089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (223253089, 1)] : List FactorBlock).map factorBlockValue).prod) = 6251086493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_223253089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6251086493) ^ 3125543246 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6251086493) ^ 893012356 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6251086493) ^ 28 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6264053953 : Nat.Prime 6264053953 := by
  apply lucas_primality 6264053953 (5 : ZMod 6264053953)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 2), (71, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 2), (71, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) = 6264053953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_71
      · exact prime_oneHundredThirtyFourEB_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6264053953) ^ 3132026976 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6264053953) ^ 2088017984 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6264053953) ^ 481850304 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6264053953) ^ 88226112 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6264053953) ^ 2303808 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6300513133 : Nat.Prime 6300513133 := by
  apply lucas_primality 6300513133 (5 : ZMod 6300513133)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (12805921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (12805921, 1)] : List FactorBlock).map factorBlockValue).prod) = 6300513133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_12805921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6300513133) ^ 3150256566 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6300513133) ^ 2100171044 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6300513133) ^ 153671052 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6300513133) ^ 492 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_8897178247 : Nat.Prime 8897178247 := by
  apply lucas_primality 8897178247 (3 : ZMod 8897178247)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (3135017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (3135017, 1)] : List FactorBlock).map factorBlockValue).prod) = 8897178247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_3135017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8897178247) ^ 4448589123 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8897178247) ^ 2965726082 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8897178247) ^ 808834386 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8897178247) ^ 206911122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8897178247) ^ 2838 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_9661502681 : Nat.Prime 9661502681 := by
  apply lucas_primality 9661502681 (3 : ZMod 9661502681)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (241537567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (241537567, 1)] : List FactorBlock).map factorBlockValue).prod) = 9661502681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_241537567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9661502681) ^ 4830751340 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9661502681) ^ 1932300536 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9661502681) ^ 40 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_11772942491 : Nat.Prime 11772942491 := by
  apply lucas_primality 11772942491 (7 : ZMod 11772942491)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (131, 1), (739, 1), (12161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (131, 1), (739, 1), (12161, 1)] : List FactorBlock).map factorBlockValue).prod) = 11772942491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_131
      · exact prime_oneHundredThirtyFourEB_739
      · exact prime_oneHundredThirtyFourEB_12161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11772942491) ^ 5886471245 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11772942491) ^ 2354588498 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11772942491) ^ 89869790 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11772942491) ^ 15930910 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11772942491) ^ 968090 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_16526450869 : Nat.Prime 16526450869 := by
  apply lucas_primality 16526450869 (10 : ZMod 16526450869)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1377204239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1377204239, 1)] : List FactorBlock).map factorBlockValue).prod) = 16526450869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1377204239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 16526450869) ^ 8263225434 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 16526450869) ^ 5508816956 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 16526450869) ^ 12 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_18501759973 : Nat.Prime 18501759973 := by
  apply lucas_primality 18501759973 (2 : ZMod 18501759973)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (513937777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (513937777, 1)] : List FactorBlock).map factorBlockValue).prod) = 18501759973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_513937777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18501759973) ^ 9250879986 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 18501759973) ^ 6167253324 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 18501759973) ^ 36 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_19279858943 : Nat.Prime 19279858943 := by
  apply lucas_primality 19279858943 (5 : ZMod 19279858943)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (12374749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (12374749, 1)] : List FactorBlock).map factorBlockValue).prod) = 19279858943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_12374749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19279858943) ^ 9639929471 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19279858943) ^ 1014729418 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19279858943) ^ 470240462 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19279858943) ^ 1558 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_19310050471 : Nat.Prime 19310050471 := by
  apply lucas_primality 19310050471 (3 : ZMod 19310050471)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1783, 1), (361003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1783, 1), (361003, 1)] : List FactorBlock).map factorBlockValue).prod) = 19310050471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_1783
      · exact prime_oneHundredThirtyFourEB_361003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19310050471) ^ 9655025235 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19310050471) ^ 6436683490 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19310050471) ^ 3862010094 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19310050471) ^ 10830090 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19310050471) ^ 53490 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_25531691657 : Nat.Prime 25531691657 := by
  apply lucas_primality 25531691657 (3 : ZMod 25531691657)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3137, 1), (1017361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3137, 1), (1017361, 1)] : List FactorBlock).map factorBlockValue).prod) = 25531691657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3137
      · exact prime_oneHundredThirtyFourEB_1017361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25531691657) ^ 12765845828 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 25531691657) ^ 8138888 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 25531691657) ^ 25096 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_25955191057 : Nat.Prime 25955191057 := by
  apply lucas_primality 25955191057 (5 : ZMod 25955191057)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1033, 1), (523459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1033, 1), (523459, 1)] : List FactorBlock).map factorBlockValue).prod) = 25955191057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1033
      · exact prime_oneHundredThirtyFourEB_523459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 25955191057) ^ 12977595528 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25955191057) ^ 8651730352 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25955191057) ^ 25126032 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25955191057) ^ 49584 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_26346871739 : Nat.Prime 26346871739 := by
  apply lucas_primality 26346871739 (2 : ZMod 26346871739)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1553, 1), (771143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1553, 1), (771143, 1)] : List FactorBlock).map factorBlockValue).prod) = 26346871739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_1553
      · exact prime_oneHundredThirtyFourEB_771143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26346871739) ^ 13173435869 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26346871739) ^ 2395170158 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26346871739) ^ 16965146 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26346871739) ^ 34166 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_31290268661 : Nat.Prime 31290268661 := by
  apply lucas_primality 31290268661 (2 : ZMod 31290268661)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (12281, 1), (18199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (12281, 1), (18199, 1)] : List FactorBlock).map factorBlockValue).prod) = 31290268661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_12281
      · exact prime_oneHundredThirtyFourEB_18199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31290268661) ^ 15645134330 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290268661) ^ 6258053732 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290268661) ^ 4470038380 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290268661) ^ 2547860 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290268661) ^ 1719340 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_31700929921 : Nat.Prime 31700929921 := by
  apply lucas_primality 31700929921 (7 : ZMod 31700929921)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (11, 1), (1500991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (11, 1), (1500991, 1)] : List FactorBlock).map factorBlockValue).prod) = 31700929921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_1500991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31700929921) ^ 15850464960 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31700929921) ^ 10566976640 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31700929921) ^ 6340185984 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31700929921) ^ 2881902720 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31700929921) ^ 21120 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_33274412377 : Nat.Prime 33274412377 := by
  apply lucas_primality 33274412377 (7 : ZMod 33274412377)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1386433849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1386433849, 1)] : List FactorBlock).map factorBlockValue).prod) = 33274412377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1386433849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 33274412377) ^ 16637206188 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 33274412377) ^ 11091470792 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 33274412377) ^ 24 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_38559717887 : Nat.Prime 38559717887 := by
  apply lucas_primality 38559717887 (5 : ZMod 38559717887)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19279858943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19279858943, 1)] : List FactorBlock).map factorBlockValue).prod) = 38559717887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_19279858943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 38559717887) ^ 19279858943 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559717887) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_39237971077 : Nat.Prime 39237971077 := by
  apply lucas_primality 39237971077 (2 : ZMod 39237971077)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (137, 1), (294659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (137, 1), (294659, 1)] : List FactorBlock).map factorBlockValue).prod) = 39237971077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_137
      · exact prime_oneHundredThirtyFourEB_294659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39237971077) ^ 19618985538 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39237971077) ^ 13079323692 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39237971077) ^ 286408548 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39237971077) ^ 133164 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_43298637929 : Nat.Prime 43298637929 := by
  apply lucas_primality 43298637929 (3 : ZMod 43298637929)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 3), (13, 1), (179, 1), (6781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 3), (13, 1), (179, 1), (6781, 1)] : List FactorBlock).map factorBlockValue).prod) = 43298637929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_179
      · exact prime_oneHundredThirtyFourEB_6781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43298637929) ^ 21649318964 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 43298637929) ^ 6185519704 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 43298637929) ^ 3330664456 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 43298637929) ^ 241891832 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 43298637929) ^ 6385288 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_44555316283 : Nat.Prime 44555316283 := by
  apply lucas_primality 44555316283 (2 : ZMod 44555316283)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (829, 1), (2985881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (829, 1), (2985881, 1)] : List FactorBlock).map factorBlockValue).prod) = 44555316283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_829
      · exact prime_oneHundredThirtyFourEB_2985881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44555316283) ^ 22277658141 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44555316283) ^ 14851772094 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44555316283) ^ 53745858 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44555316283) ^ 14922 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_49052936551 : Nat.Prime 49052936551 := by
  apply lucas_primality 49052936551 (3 : ZMod 49052936551)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (327019577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (327019577, 1)] : List FactorBlock).map factorBlockValue).prod) = 49052936551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_327019577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49052936551) ^ 24526468275 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49052936551) ^ 16350978850 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49052936551) ^ 9810587310 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49052936551) ^ 150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_51436664287 : Nat.Prime 51436664287 := by
  apply lucas_primality 51436664287 (3 : ZMod 51436664287)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1224682483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1224682483, 1)] : List FactorBlock).map factorBlockValue).prod) = 51436664287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_1224682483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51436664287) ^ 25718332143 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 51436664287) ^ 17145554762 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 51436664287) ^ 7348094898 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 51436664287) ^ 42 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_54887354219 : Nat.Prime 54887354219 := by
  apply lucas_primality 54887354219 (2 : ZMod 54887354219)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (251, 1), (3643, 1), (30013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (251, 1), (3643, 1), (30013, 1)] : List FactorBlock).map factorBlockValue).prod) = 54887354219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_251
      · exact prime_oneHundredThirtyFourEB_3643
      · exact prime_oneHundredThirtyFourEB_30013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54887354219) ^ 27443677109 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54887354219) ^ 218674718 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54887354219) ^ 15066526 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54887354219) ^ 1828786 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_54983748661 : Nat.Prime 54983748661 := by
  apply lucas_primality 54983748661 (2 : ZMod 54983748661)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (53, 1), (17290487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (53, 1), (17290487, 1)] : List FactorBlock).map factorBlockValue).prod) = 54983748661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_53
      · exact prime_oneHundredThirtyFourEB_17290487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54983748661) ^ 27491874330 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54983748661) ^ 18327916220 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54983748661) ^ 10996749732 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54983748661) ^ 1037429220 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54983748661) ^ 3180 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_66011526197 : Nat.Prime 66011526197 := by
  apply lucas_primality 66011526197 (2 : ZMod 66011526197)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (29, 1), (43, 2), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (29, 1), (43, 2), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 66011526197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66011526197) ^ 33005763098 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66011526197) ^ 9430218028 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66011526197) ^ 6001047836 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66011526197) ^ 2276259524 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66011526197) ^ 1535151772 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66011526197) ^ 115606876 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_68016083159 : Nat.Prime 68016083159 := by
  apply lucas_primality 68016083159 (13 : ZMod 68016083159)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (281, 1), (506381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (281, 1), (506381, 1)] : List FactorBlock).map factorBlockValue).prod) = 68016083159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_239
      · exact prime_oneHundredThirtyFourEB_281
      · exact prime_oneHundredThirtyFourEB_506381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 68016083159) ^ 34008041579 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 68016083159) ^ 284586122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 68016083159) ^ 242050118 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 68016083159) ^ 134318 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_83558062409 : Nat.Prime 83558062409 := by
  apply lucas_primality 83558062409 (3 : ZMod 83558062409)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (439, 1), (767489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (439, 1), (767489, 1)] : List FactorBlock).map factorBlockValue).prod) = 83558062409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_439
      · exact prime_oneHundredThirtyFourEB_767489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 83558062409) ^ 41779031204 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 83558062409) ^ 2695421368 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 83558062409) ^ 190337272 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 83558062409) ^ 108872 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_84398187563 : Nat.Prime 84398187563 := by
  apply lucas_primality 84398187563 (2 : ZMod 84398187563)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3246084137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3246084137, 1)] : List FactorBlock).map factorBlockValue).prod) = 84398187563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_3246084137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84398187563) ^ 42199093781 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 84398187563) ^ 6492168274 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 84398187563) ^ 26 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_90963727199 : Nat.Prime 90963727199 := by
  apply lucas_primality 90963727199 (7 : ZMod 90963727199)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (6359, 1), (7019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (6359, 1), (7019, 1)] : List FactorBlock).map factorBlockValue).prod) = 90963727199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1019
      · exact prime_oneHundredThirtyFourEB_6359
      · exact prime_oneHundredThirtyFourEB_7019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 90963727199) ^ 45481863599 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 90963727199) ^ 89267642 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 90963727199) ^ 14304722 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 90963727199) ^ 12959642 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_116230282141 : Nat.Prime 116230282141 := by
  apply lucas_primality 116230282141 (2 : ZMod 116230282141)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (31, 1), (137, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (31, 1), (137, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) = 116230282141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_137
      · exact prime_oneHundredThirtyFourEB_3833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116230282141) ^ 58115141070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 38743427380 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 23246056428 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 16604326020 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 6837075420 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 3749363940 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 848396220 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116230282141) ^ 30323580 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_120193771681 : Nat.Prime 120193771681 := by
  apply lucas_primality 120193771681 (29 : ZMod 120193771681)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (23, 1), (3629039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (23, 1), (3629039, 1)] : List FactorBlock).map factorBlockValue).prod) = 120193771681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_3629039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 120193771681) ^ 60096885840 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (29 : ZMod 120193771681) ^ 40064590560 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (29 : ZMod 120193771681) ^ 24038754336 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (29 : ZMod 120193771681) ^ 5225816160 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (29 : ZMod 120193771681) ^ 33120 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_123952865149 : Nat.Prime 123952865149 := by
  apply lucas_primality 123952865149 (2 : ZMod 123952865149)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (491876449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (491876449, 1)] : List FactorBlock).map factorBlockValue).prod) = 123952865149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_491876449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123952865149) ^ 61976432574 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123952865149) ^ 41317621716 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123952865149) ^ 17707552164 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123952865149) ^ 252 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_149588699023 : Nat.Prime 149588699023 := by
  apply lucas_primality 149588699023 (5 : ZMod 149588699023)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (7, 1), (43, 1), (340859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (7, 1), (43, 1), (340859, 1)] : List FactorBlock).map factorBlockValue).prod) = 149588699023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_340859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 149588699023) ^ 74794349511 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149588699023) ^ 49862899674 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149588699023) ^ 21369814146 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149588699023) ^ 3478806954 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149588699023) ^ 438858 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_171971281987 : Nat.Prime 171971281987 := by
  apply lucas_primality 171971281987 (13 : ZMod 171971281987)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (25541, 1), (160313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (25541, 1), (160313, 1)] : List FactorBlock).map factorBlockValue).prod) = 171971281987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_25541
      · exact prime_oneHundredThirtyFourEB_160313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 171971281987) ^ 85985640993 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 171971281987) ^ 57323760662 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 171971281987) ^ 24567325998 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 171971281987) ^ 6733146 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 171971281987) ^ 1072722 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_225704648761 : Nat.Prime 225704648761 := by
  apply lucas_primality 225704648761 (13 : ZMod 225704648761)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (43, 1), (2302169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (43, 1), (2302169, 1)] : List FactorBlock).map factorBlockValue).prod) = 225704648761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_2302169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 225704648761) ^ 112852324380 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 225704648761) ^ 75234882920 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 225704648761) ^ 45140929752 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 225704648761) ^ 11879192040 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 225704648761) ^ 5248945320 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 225704648761) ^ 98040 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_348168523819 : Nat.Prime 348168523819 := by
  apply lucas_primality 348168523819 (2 : ZMod 348168523819)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7213, 1), (8044931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7213, 1), (8044931, 1)] : List FactorBlock).map factorBlockValue).prod) = 348168523819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7213
      · exact prime_oneHundredThirtyFourEB_8044931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 348168523819) ^ 174084261909 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 348168523819) ^ 116056174606 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 348168523819) ^ 48269586 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 348168523819) ^ 43278 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_403643834681 : Nat.Prime 403643834681 := by
  apply lucas_primality 403643834681 (3 : ZMod 403643834681)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (347968823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (347968823, 1)] : List FactorBlock).map factorBlockValue).prod) = 403643834681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_347968823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 403643834681) ^ 201821917340 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 403643834681) ^ 80728766936 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 403643834681) ^ 13918752920 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 403643834681) ^ 1160 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_440439633889 : Nat.Prime 440439633889 := by
  apply lucas_primality 440439633889 (13 : ZMod 440439633889)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (4587912853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (4587912853, 1)] : List FactorBlock).map factorBlockValue).prod) = 440439633889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_4587912853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 440439633889) ^ 220219816944 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 440439633889) ^ 146813211296 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 440439633889) ^ 96 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_462099215603 : Nat.Prime 462099215603 := by
  apply lucas_primality 462099215603 (2 : ZMod 462099215603)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (6733, 1), (385573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (6733, 1), (385573, 1)] : List FactorBlock).map factorBlockValue).prod) = 462099215603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_89
      · exact prime_oneHundredThirtyFourEB_6733
      · exact prime_oneHundredThirtyFourEB_385573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 462099215603) ^ 231049607801 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 462099215603) ^ 5192126018 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 462099215603) ^ 68631994 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 462099215603) ^ 1198474 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_464934984089 : Nat.Prime 464934984089 := by
  apply lucas_primality 464934984089 (3 : ZMod 464934984089)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (1236529213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (1236529213, 1)] : List FactorBlock).map factorBlockValue).prod) = 464934984089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_1236529213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 464934984089) ^ 232467492044 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 464934984089) ^ 9892233704 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 464934984089) ^ 376 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_473237305559 : Nat.Prime 473237305559 := by
  apply lucas_primality 473237305559 (7 : ZMod 473237305559)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (920695147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (920695147, 1)] : List FactorBlock).map factorBlockValue).prod) = 473237305559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_257
      · exact prime_oneHundredThirtyFourEB_920695147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 473237305559) ^ 236618652779 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 473237305559) ^ 1841390294 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 473237305559) ^ 514 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_562165370891 : Nat.Prime 562165370891 := by
  apply lucas_primality 562165370891 (2 : ZMod 562165370891)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (809, 1), (69488921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (809, 1), (69488921, 1)] : List FactorBlock).map factorBlockValue).prod) = 562165370891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_809
      · exact prime_oneHundredThirtyFourEB_69488921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 562165370891) ^ 281082685445 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 562165370891) ^ 112433074178 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 562165370891) ^ 694889210 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 562165370891) ^ 8090 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_666835464193 : Nat.Prime 666835464193 := by
  apply lucas_primality 666835464193 (5 : ZMod 666835464193)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 1), (593, 1), (91513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 1), (593, 1), (91513, 1)] : List FactorBlock).map factorBlockValue).prod) = 666835464193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_593
      · exact prime_oneHundredThirtyFourEB_91513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 666835464193) ^ 333417732096 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 666835464193) ^ 222278488064 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 666835464193) ^ 1124511744 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 666835464193) ^ 7286784 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1124330741783 : Nat.Prime 1124330741783 := by
  apply lucas_primality 1124330741783 (5 : ZMod 1124330741783)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (562165370891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (562165370891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1124330741783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_562165370891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1124330741783) ^ 562165370891 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1124330741783) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1141662848551 : Nat.Prime 1141662848551 := by
  apply lucas_primality 1141662848551 (3 : ZMod 1141662848551)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (181, 1), (449, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (181, 1), (449, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141662848551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_181
      · exact prime_oneHundredThirtyFourEB_449
      · exact prime_oneHundredThirtyFourEB_787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1141662848551) ^ 570831424275 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 380554282850 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 228332569710 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 163094692650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 67156638150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 6307529550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 2542678950 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141662848551) ^ 1450651650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1193331682783 : Nat.Prime 1193331682783 := by
  apply lucas_primality 1193331682783 (5 : ZMod 1193331682783)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (1277, 1), (625489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (1277, 1), (625489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1193331682783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_83
      · exact prime_oneHundredThirtyFourEB_1277
      · exact prime_oneHundredThirtyFourEB_625489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1193331682783) ^ 596665841391 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1193331682783) ^ 397777227594 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1193331682783) ^ 14377490154 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1193331682783) ^ 934480566 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1193331682783) ^ 1907838 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1228307357573 : Nat.Prime 1228307357573 := by
  apply lucas_primality 1228307357573 (2 : ZMod 1228307357573)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (283, 1), (1085077171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (283, 1), (1085077171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1228307357573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_283
      · exact prime_oneHundredThirtyFourEB_1085077171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1228307357573) ^ 614153678786 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1228307357573) ^ 4340308684 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1228307357573) ^ 1132 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1312752365651 : Nat.Prime 1312752365651 := by
  apply lucas_primality 1312752365651 (2 : ZMod 1312752365651)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (2386822483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (2386822483, 1)] : List FactorBlock).map factorBlockValue).prod) = 1312752365651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_2386822483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1312752365651) ^ 656376182825 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312752365651) ^ 262550473130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312752365651) ^ 119341124150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312752365651) ^ 550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1385556413729 : Nat.Prime 1385556413729 := by
  apply lucas_primality 1385556413729 (3 : ZMod 1385556413729)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (43298637929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (43298637929, 1)] : List FactorBlock).map factorBlockValue).prod) = 1385556413729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_43298637929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1385556413729) ^ 692778206864 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1385556413729) ^ 32 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1453260517097 : Nat.Prime 1453260517097 := by
  apply lucas_primality 1453260517097 (3 : ZMod 1453260517097)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (6264053953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (6264053953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1453260517097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_6264053953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1453260517097) ^ 726630258548 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1453260517097) ^ 50112431624 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1453260517097) ^ 232 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1520637217199 : Nat.Prime 1520637217199 := by
  apply lucas_primality 1520637217199 (7 : ZMod 1520637217199)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (601, 1), (3709939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (601, 1), (3709939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1520637217199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_601
      · exact prime_oneHundredThirtyFourEB_3709939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1520637217199) ^ 760318608599 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1520637217199) ^ 138239747018 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1520637217199) ^ 49052813458 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1520637217199) ^ 2530178398 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1520637217199) ^ 409882 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1539544962509 : Nat.Prime 1539544962509 := by
  apply lucas_primality 1539544962509 (2 : ZMod 1539544962509)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (54983748661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (54983748661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1539544962509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_54983748661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1539544962509) ^ 769772481254 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1539544962509) ^ 219934994644 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1539544962509) ^ 28 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1564513433051 : Nat.Prime 1564513433051 := by
  apply lucas_primality 1564513433051 (2 : ZMod 1564513433051)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31290268661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31290268661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564513433051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_31290268661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1564513433051) ^ 782256716525 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564513433051) ^ 312902686610 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564513433051) ^ 50 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1607998566547 : Nat.Prime 1607998566547 := by
  apply lucas_primality 1607998566547 (2 : ZMod 1607998566547)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (173, 1), (5059, 1), (102071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (173, 1), (5059, 1), (102071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1607998566547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_173
      · exact prime_oneHundredThirtyFourEB_5059
      · exact prime_oneHundredThirtyFourEB_102071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1607998566547) ^ 803999283273 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607998566547) ^ 535999522182 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607998566547) ^ 9294789402 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607998566547) ^ 317849094 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607998566547) ^ 15753726 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1795064388277 : Nat.Prime 1795064388277 := by
  apply lucas_primality 1795064388277 (5 : ZMod 1795064388277)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149588699023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149588699023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1795064388277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_149588699023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1795064388277) ^ 897532194138 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1795064388277) ^ 598354796092 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1795064388277) ^ 12 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2276410728653 : Nat.Prime 2276410728653 := by
  apply lucas_primality 2276410728653 (2 : ZMod 2276410728653)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (499, 1), (1140486337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (499, 1), (1140486337, 1)] : List FactorBlock).map factorBlockValue).prod) = 2276410728653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_499
      · exact prime_oneHundredThirtyFourEB_1140486337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2276410728653) ^ 1138205364326 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2276410728653) ^ 4561945348 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2276410728653) ^ 1996 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2456614715147 : Nat.Prime 2456614715147 := by
  apply lucas_primality 2456614715147 (2 : ZMod 2456614715147)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1228307357573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1228307357573, 1)] : List FactorBlock).map factorBlockValue).prod) = 2456614715147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1228307357573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2456614715147) ^ 1228307357573 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2456614715147) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2983326528647 : Nat.Prime 2983326528647 := by
  apply lucas_primality 2983326528647 (5 : ZMod 2983326528647)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (51436664287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (51436664287, 1)] : List FactorBlock).map factorBlockValue).prod) = 2983326528647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_51436664287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2983326528647) ^ 1491663264323 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2983326528647) ^ 102873328574 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2983326528647) ^ 58 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4618414461467 : Nat.Prime 4618414461467 := by
  apply lucas_primality 4618414461467 (2 : ZMod 4618414461467)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (3779389903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (3779389903, 1)] : List FactorBlock).map factorBlockValue).prod) = 4618414461467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_3779389903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4618414461467) ^ 2309207230733 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618414461467) ^ 355262650882 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618414461467) ^ 98264137478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618414461467) ^ 1222 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4627140549947 : Nat.Prime 4627140549947 := by
  apply lucas_primality 4627140549947 (2 : ZMod 4627140549947)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5107, 1), (453019439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5107, 1), (453019439, 1)] : List FactorBlock).map factorBlockValue).prod) = 4627140549947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5107
      · exact prime_oneHundredThirtyFourEB_453019439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4627140549947) ^ 2313570274973 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4627140549947) ^ 906038878 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4627140549947) ^ 10214 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_5432433911087 : Nat.Prime 5432433911087 := by
  apply lucas_primality 5432433911087 (5 : ZMod 5432433911087)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (809, 1), (36895597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (809, 1), (36895597, 1)] : List FactorBlock).map factorBlockValue).prod) = 5432433911087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_809
      · exact prime_oneHundredThirtyFourEB_36895597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5432433911087) ^ 2716216955543 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5432433911087) ^ 776061987298 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5432433911087) ^ 417879531622 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5432433911087) ^ 6714998654 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5432433911087) ^ 147238 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6616258056431 : Nat.Prime 6616258056431 := by
  apply lucas_primality 6616258056431 (11 : ZMod 6616258056431)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (18583, 1), (3236711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (18583, 1), (3236711, 1)] : List FactorBlock).map factorBlockValue).prod) = 6616258056431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_18583
      · exact prime_oneHundredThirtyFourEB_3236711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6616258056431) ^ 3308129028215 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 6616258056431) ^ 1323251611286 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 6616258056431) ^ 601478005130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 6616258056431) ^ 356038210 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 6616258056431) ^ 2044130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_14614558068223 : Nat.Prime 14614558068223 := by
  apply lucas_primality 14614558068223 (6 : ZMod 14614558068223)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (27073, 1), (252017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (27073, 1), (252017, 1)] : List FactorBlock).map factorBlockValue).prod) = 14614558068223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_27073
      · exact prime_oneHundredThirtyFourEB_252017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14614558068223) ^ 7307279034111 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14614558068223) ^ 4871519356074 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14614558068223) ^ 2087794009746 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14614558068223) ^ 859679886366 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14614558068223) ^ 539820414 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14614558068223) ^ 57990366 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_21317765085509 : Nat.Prime 21317765085509 := by
  apply lucas_primality 21317765085509 (2 : ZMod 21317765085509)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (3881, 1), (44297207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (3881, 1), (44297207, 1)] : List FactorBlock).map factorBlockValue).prod) = 21317765085509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_3881
      · exact prime_oneHundredThirtyFourEB_44297207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21317765085509) ^ 10658882542754 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 21317765085509) ^ 687669841468 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 21317765085509) ^ 5492853668 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 21317765085509) ^ 481244 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_32766533662817 : Nat.Prime 32766533662817 := by
  apply lucas_primality 32766533662817 (3 : ZMod 32766533662817)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (251, 1), (4079498713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (251, 1), (4079498713, 1)] : List FactorBlock).map factorBlockValue).prod) = 32766533662817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_251
      · exact prime_oneHundredThirtyFourEB_4079498713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32766533662817) ^ 16383266831408 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32766533662817) ^ 130543958816 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32766533662817) ^ 8032 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_46795560030367 : Nat.Prime 46795560030367 := by
  apply lucas_primality 46795560030367 (5 : ZMod 46795560030367)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2917, 1), (381960919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2917, 1), (381960919, 1)] : List FactorBlock).map factorBlockValue).prod) = 46795560030367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_2917
      · exact prime_oneHundredThirtyFourEB_381960919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 46795560030367) ^ 23397780015183 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 46795560030367) ^ 15598520010122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 46795560030367) ^ 6685080004338 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 46795560030367) ^ 16042358598 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 46795560030367) ^ 122514 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_47924368019023 : Nat.Prime 47924368019023 := by
  apply lucas_primality 47924368019023 (3 : ZMod 47924368019023)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (66011526197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (66011526197, 1)] : List FactorBlock).map factorBlockValue).prod) = 47924368019023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_66011526197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 47924368019023) ^ 23962184009511 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47924368019023) ^ 15974789339674 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47924368019023) ^ 4356760729002 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47924368019023) ^ 726 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_52288486450637 : Nat.Prime 52288486450637 := by
  apply lucas_primality 52288486450637 (2 : ZMod 52288486450637)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (281, 1), (691, 1), (1741, 1), (38669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (281, 1), (691, 1), (1741, 1), (38669, 1)] : List FactorBlock).map factorBlockValue).prod) = 52288486450637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_281
      · exact prime_oneHundredThirtyFourEB_691
      · exact prime_oneHundredThirtyFourEB_1741
      · exact prime_oneHundredThirtyFourEB_38669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52288486450637) ^ 26144243225318 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52288486450637) ^ 186080022956 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52288486450637) ^ 75670747396 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52288486450637) ^ 30033593596 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52288486450637) ^ 1352206844 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_54768862156133 : Nat.Prime 54768862156133 := by
  apply lucas_primality 54768862156133 (2 : ZMod 54768862156133)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3967, 1), (6221, 1), (29201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3967, 1), (6221, 1), (29201, 1)] : List FactorBlock).map factorBlockValue).prod) = 54768862156133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_3967
      · exact prime_oneHundredThirtyFourEB_6221
      · exact prime_oneHundredThirtyFourEB_29201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54768862156133) ^ 27384431078066 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54768862156133) ^ 2882571692428 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54768862156133) ^ 13806115996 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54768862156133) ^ 8803867892 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54768862156133) ^ 1875581732 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_63749956565101 : Nat.Prime 63749956565101 := by
  apply lucas_primality 63749956565101 (2 : ZMod 63749956565101)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 2), (191, 1), (631, 1), (10433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 2), (191, 1), (631, 1), (10433, 1)] : List FactorBlock).map factorBlockValue).prod) = 63749956565101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_191
      · exact prime_oneHundredThirtyFourEB_631
      · exact prime_oneHundredThirtyFourEB_10433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63749956565101) ^ 31874978282550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63749956565101) ^ 21249985521700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63749956565101) ^ 12749991313020 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63749956565101) ^ 4903842812700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63749956565101) ^ 333769406100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63749956565101) ^ 101030042100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 63749956565101) ^ 6110414700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_67103671346627 : Nat.Prime 67103671346627 := by
  apply lucas_primality 67103671346627 (2 : ZMod 67103671346627)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (809, 1), (1120897861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (809, 1), (1120897861, 1)] : List FactorBlock).map factorBlockValue).prod) = 67103671346627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_37
      · exact prime_oneHundredThirtyFourEB_809
      · exact prime_oneHundredThirtyFourEB_1120897861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67103671346627) ^ 33551835673313 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67103671346627) ^ 1813612739098 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67103671346627) ^ 82946441714 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67103671346627) ^ 59866 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_69708505990547 : Nat.Prime 69708505990547 := by
  apply lucas_primality 69708505990547 (2 : ZMod 69708505990547)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1124330741783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1124330741783, 1)] : List FactorBlock).map factorBlockValue).prod) = 69708505990547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_1124330741783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 69708505990547) ^ 34854252995273 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 69708505990547) ^ 2248661483566 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 69708505990547) ^ 62 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_79862738360611 : Nat.Prime 79862738360611 := by
  apply lucas_primality 79862738360611 (2 : ZMod 79862738360611)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (239, 1), (29947, 1), (371939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (239, 1), (29947, 1), (371939, 1)] : List FactorBlock).map factorBlockValue).prod) = 79862738360611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_239
      · exact prime_oneHundredThirtyFourEB_29947
      · exact prime_oneHundredThirtyFourEB_371939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79862738360611) ^ 39931369180305 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79862738360611) ^ 26620912786870 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79862738360611) ^ 15972547672122 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79862738360611) ^ 334153716990 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79862738360611) ^ 2666802630 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79862738360611) ^ 214719990 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_127471190063069 : Nat.Prime 127471190063069 := by
  apply lucas_primality 127471190063069 (2 : ZMod 127471190063069)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1385556413729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1385556413729, 1)] : List FactorBlock).map factorBlockValue).prod) = 127471190063069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_1385556413729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 127471190063069) ^ 63735595031534 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 127471190063069) ^ 5542225654916 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 127471190063069) ^ 92 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_140216944498913 : Nat.Prime 140216944498913 := by
  apply lucas_primality 140216944498913 (3 : ZMod 140216944498913)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19597, 1), (223594403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19597, 1), (223594403, 1)] : List FactorBlock).map factorBlockValue).prod) = 140216944498913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_19597
      · exact prime_oneHundredThirtyFourEB_223594403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 140216944498913) ^ 70108472249456 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 140216944498913) ^ 7155020896 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 140216944498913) ^ 627104 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_170152244985427 : Nat.Prime 170152244985427 := by
  apply lucas_primality 170152244985427 (3 : ZMod 170152244985427)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (17, 1), (691, 1), (19951433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (17, 1), (691, 1), (19951433, 1)] : List FactorBlock).map factorBlockValue).prod) = 170152244985427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_691
      · exact prime_oneHundredThirtyFourEB_19951433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 170152244985427) ^ 85076122492713 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 170152244985427) ^ 56717414995142 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 170152244985427) ^ 15468385907766 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 170152244985427) ^ 10008955587378 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 170152244985427) ^ 246240586086 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 170152244985427) ^ 8528322 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_175254846950641 : Nat.Prime 175254846950641 := by
  apply lucas_primality 175254846950641 (7 : ZMod 175254846950641)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (32603, 1), (22397587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (32603, 1), (22397587, 1)] : List FactorBlock).map factorBlockValue).prod) = 175254846950641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_32603
      · exact prime_oneHundredThirtyFourEB_22397587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 175254846950641) ^ 87627423475320 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 175254846950641) ^ 58418282316880 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 175254846950641) ^ 35050969390128 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 175254846950641) ^ 5375420880 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 175254846950641) ^ 7824720 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_187182240121469 : Nat.Prime 187182240121469 := by
  apply lucas_primality 187182240121469 (2 : ZMod 187182240121469)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (46795560030367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (46795560030367, 1)] : List FactorBlock).map factorBlockValue).prod) = 187182240121469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_46795560030367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 187182240121469) ^ 93591120060734 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 187182240121469) ^ 4 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_193862281093037 : Nat.Prime 193862281093037 := by
  apply lucas_primality 193862281093037 (2 : ZMod 193862281093037)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (123952865149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (123952865149, 1)] : List FactorBlock).map factorBlockValue).prod) = 193862281093037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_123952865149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193862281093037) ^ 96931140546518 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 193862281093037) ^ 11403663593708 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 193862281093037) ^ 8428794830132 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 193862281093037) ^ 1564 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_212655046437161 : Nat.Prime 212655046437161 := by
  apply lucas_primality 212655046437161 (3 : ZMod 212655046437161)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1319, 1), (23629, 1), (170579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1319, 1), (23629, 1), (170579, 1)] : List FactorBlock).map factorBlockValue).prod) = 212655046437161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_1319
      · exact prime_oneHundredThirtyFourEB_23629
      · exact prime_oneHundredThirtyFourEB_170579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 212655046437161) ^ 106327523218580 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 212655046437161) ^ 42531009287432 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 212655046437161) ^ 161224447640 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 212655046437161) ^ 8999748040 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 212655046437161) ^ 1246666040 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_256979893031339 : Nat.Prime 256979893031339 := by
  apply lucas_primality 256979893031339 (2 : ZMod 256979893031339)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (569417, 1), (2535413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (569417, 1), (2535413, 1)] : List FactorBlock).map factorBlockValue).prod) = 256979893031339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_89
      · exact prime_oneHundredThirtyFourEB_569417
      · exact prime_oneHundredThirtyFourEB_2535413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 256979893031339) ^ 128489946515669 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256979893031339) ^ 2887414528442 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256979893031339) ^ 451303514 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256979893031339) ^ 101356226 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_298448711197127 : Nat.Prime 298448711197127 := by
  apply lucas_primality 298448711197127 (5 : ZMod 298448711197127)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (21317765085509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (21317765085509, 1)] : List FactorBlock).map factorBlockValue).prod) = 298448711197127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_21317765085509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 298448711197127) ^ 149224355598563 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 298448711197127) ^ 42635530171018 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 298448711197127) ^ 14 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_374364480242939 : Nat.Prime 374364480242939 := by
  apply lucas_primality 374364480242939 (2 : ZMod 374364480242939)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (187182240121469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (187182240121469, 1)] : List FactorBlock).map factorBlockValue).prod) = 374364480242939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_187182240121469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 374364480242939) ^ 187182240121469 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 374364480242939) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_530824079736563 : Nat.Prime 530824079736563 := by
  apply lucas_primality 530824079736563 (2 : ZMod 530824079736563)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (89, 1), (251, 1), (194772239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (89, 1), (251, 1), (194772239, 1)] : List FactorBlock).map factorBlockValue).prod) = 530824079736563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_61
      · exact prime_oneHundredThirtyFourEB_89
      · exact prime_oneHundredThirtyFourEB_251
      · exact prime_oneHundredThirtyFourEB_194772239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 530824079736563) ^ 265412039868281 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 530824079736563) ^ 8702034094042 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 530824079736563) ^ 5964315502658 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 530824079736563) ^ 2114836971062 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 530824079736563) ^ 2725358 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_606721690722877 : Nat.Prime 606721690722877 := by
  apply lucas_primality 606721690722877 (2 : ZMod 606721690722877)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8419, 1), (6005480567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8419, 1), (6005480567, 1)] : List FactorBlock).map factorBlockValue).prod) = 606721690722877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_8419
      · exact prime_oneHundredThirtyFourEB_6005480567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 606721690722877) ^ 303360845361438 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 606721690722877) ^ 202240563574292 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 606721690722877) ^ 72065766804 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 606721690722877) ^ 101028 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_611336262656131 : Nat.Prime 611336262656131 := by
  apply lucas_primality 611336262656131 (11 : ZMod 611336262656131)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (937, 1), (37303601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (937, 1), (37303601, 1)] : List FactorBlock).map factorBlockValue).prod) = 611336262656131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_53
      · exact prime_oneHundredThirtyFourEB_937
      · exact prime_oneHundredThirtyFourEB_37303601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 611336262656131) ^ 305668131328065 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 611336262656131) ^ 203778754218710 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 611336262656131) ^ 122267252531226 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 611336262656131) ^ 55576023877830 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 611336262656131) ^ 11534646465210 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 611336262656131) ^ 652439981490 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 611336262656131) ^ 16388130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_903344469547829 : Nat.Prime 903344469547829 := by
  apply lucas_primality 903344469547829 (2 : ZMod 903344469547829)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (113, 1), (25955191057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (113, 1), (25955191057, 1)] : List FactorBlock).map factorBlockValue).prod) = 903344469547829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_113
      · exact prime_oneHundredThirtyFourEB_25955191057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 903344469547829) ^ 451672234773914 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 903344469547829) ^ 129049209935404 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 903344469547829) ^ 82122224504348 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 903344469547829) ^ 7994198845556 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 903344469547829) ^ 34804 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1030366958870999 : Nat.Prime 1030366958870999 := by
  apply lucas_primality 1030366958870999 (7 : ZMod 1030366958870999)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (1795064388277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (1795064388277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1030366958870999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_1795064388277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1030366958870999) ^ 515183479435499 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1030366958870999) ^ 147195279838714 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1030366958870999) ^ 25130901435878 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1030366958870999) ^ 574 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1263678983289797 : Nat.Prime 1263678983289797 := by
  apply lucas_primality 1263678983289797 (2 : ZMod 1263678983289797)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (499, 1), (3536903369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (499, 1), (3536903369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1263678983289797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_179
      · exact prime_oneHundredThirtyFourEB_499
      · exact prime_oneHundredThirtyFourEB_3536903369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1263678983289797) ^ 631839491644898 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1263678983289797) ^ 7059659124524 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1263678983289797) ^ 2532422812204 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1263678983289797) ^ 357284 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1821006852351649 : Nat.Prime 1821006852351649 := by
  apply lucas_primality 1821006852351649 (11 : ZMod 1821006852351649)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (4871, 1), (299556581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (4871, 1), (299556581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1821006852351649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_4871
      · exact prime_oneHundredThirtyFourEB_299556581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1821006852351649) ^ 910503426175824 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1821006852351649) ^ 607002284117216 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1821006852351649) ^ 140077450180896 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1821006852351649) ^ 373846613088 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1821006852351649) ^ 6079008 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2479110385407431 : Nat.Prime 2479110385407431 := by
  apply lucas_primality 2479110385407431 (17 : ZMod 2479110385407431)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (331, 1), (479, 1), (1321, 1), (31991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (331, 1), (479, 1), (1321, 1), (31991, 1)] : List FactorBlock).map factorBlockValue).prod) = 2479110385407431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_37
      · exact prime_oneHundredThirtyFourEB_331
      · exact prime_oneHundredThirtyFourEB_479
      · exact prime_oneHundredThirtyFourEB_1321
      · exact prime_oneHundredThirtyFourEB_31991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2479110385407431) ^ 1239555192703715 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (17 : ZMod 2479110385407431) ^ 495822077081486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (17 : ZMod 2479110385407431) ^ 67002983389390 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (17 : ZMod 2479110385407431) ^ 7489759472530 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (17 : ZMod 2479110385407431) ^ 5175595794170 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (17 : ZMod 2479110385407431) ^ 1876692191830 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (17 : ZMod 2479110385407431) ^ 77493994730 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2505656276001019 : Nat.Prime 2505656276001019 := by
  apply lucas_primality 2505656276001019 (3 : ZMod 2505656276001019)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (1459, 1), (1514443753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (1459, 1), (1514443753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2505656276001019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_1459
      · exact prime_oneHundredThirtyFourEB_1514443753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2505656276001019) ^ 1252828138000509 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505656276001019) ^ 835218758667006 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505656276001019) ^ 357950896571574 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505656276001019) ^ 1717379215902 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505656276001019) ^ 1654506 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3102418318302553 : Nat.Prime 3102418318302553 := by
  apply lucas_primality 3102418318302553 (10 : ZMod 3102418318302553)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (919, 1), (2992786561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (919, 1), (2992786561, 1)] : List FactorBlock).map factorBlockValue).prod) = 3102418318302553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_919
      · exact prime_oneHundredThirtyFourEB_2992786561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3102418318302553) ^ 1551209159151276 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 3102418318302553) ^ 1034139439434184 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 3102418318302553) ^ 66008900389416 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 3102418318302553) ^ 3375863240808 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 3102418318302553) ^ 1036632 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3174259426480409 : Nat.Prime 3174259426480409 := by
  apply lucas_primality 3174259426480409 (3 : ZMod 3174259426480409)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (2983326528647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (2983326528647, 1)] : List FactorBlock).map factorBlockValue).prod) = 3174259426480409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_2983326528647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3174259426480409) ^ 1587129713240204 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3174259426480409) ^ 453465632354344 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3174259426480409) ^ 167066285604232 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3174259426480409) ^ 1064 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3305703737332411 : Nat.Prime 3305703737332411 := by
  apply lucas_primality 3305703737332411 (2 : ZMod 3305703737332411)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (73, 1), (1237, 1), (18212741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (73, 1), (1237, 1), (18212741, 1)] : List FactorBlock).map factorBlockValue).prod) = 3305703737332411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_67
      · exact prime_oneHundredThirtyFourEB_73
      · exact prime_oneHundredThirtyFourEB_1237
      · exact prime_oneHundredThirtyFourEB_18212741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3305703737332411) ^ 1652851868666205 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3305703737332411) ^ 1101901245777470 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3305703737332411) ^ 661140747466482 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3305703737332411) ^ 49338861751230 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3305703737332411) ^ 45283612840170 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3305703737332411) ^ 2672355486930 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3305703737332411) ^ 181505010 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4768263011739203 : Nat.Prime 4768263011739203 := by
  apply lucas_primality 4768263011739203 (2 : ZMod 4768263011739203)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (331697, 1), (52464809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (331697, 1), (52464809, 1)] : List FactorBlock).map factorBlockValue).prod) = 4768263011739203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_137
      · exact prime_oneHundredThirtyFourEB_331697
      · exact prime_oneHundredThirtyFourEB_52464809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4768263011739203) ^ 2384131505869601 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4768263011739203) ^ 34804839501746 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4768263011739203) ^ 14375357666 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4768263011739203) ^ 90884978 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4885356419096789 : Nat.Prime 4885356419096789 := by
  apply lucas_primality 4885356419096789 (2 : ZMod 4885356419096789)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (59, 1), (440439633889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (59, 1), (440439633889, 1)] : List FactorBlock).map factorBlockValue).prod) = 4885356419096789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_59
      · exact prime_oneHundredThirtyFourEB_440439633889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4885356419096789) ^ 2442678209548394 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4885356419096789) ^ 103943753597804 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4885356419096789) ^ 82802651171132 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4885356419096789) ^ 11092 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_5918667894497801 : Nat.Prime 5918667894497801 := by
  apply lucas_primality 5918667894497801 (6 : ZMod 5918667894497801)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (2276410728653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (2276410728653, 1)] : List FactorBlock).map factorBlockValue).prod) = 5918667894497801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_2276410728653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5918667894497801) ^ 2959333947248900 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5918667894497801) ^ 1183733578899560 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5918667894497801) ^ 455282145730600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5918667894497801) ^ 2600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6899720629650377 : Nat.Prime 6899720629650377 := by
  apply lucas_primality 6899720629650377 (3 : ZMod 6899720629650377)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (929, 1), (84398187563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (929, 1), (84398187563, 1)] : List FactorBlock).map factorBlockValue).prod) = 6899720629650377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_929
      · exact prime_oneHundredThirtyFourEB_84398187563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6899720629650377) ^ 3449860314825188 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6899720629650377) ^ 627247329968216 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6899720629650377) ^ 7427040505544 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6899720629650377) ^ 81752 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_7284027409406597 : Nat.Prime 7284027409406597 := by
  apply lucas_primality 7284027409406597 (2 : ZMod 7284027409406597)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1821006852351649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1821006852351649, 1)] : List FactorBlock).map factorBlockValue).prod) = 7284027409406597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1821006852351649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7284027409406597) ^ 3642013704703298 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7284027409406597) ^ 4 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_8346308408302637 : Nat.Prime 8346308408302637 := by
  apply lucas_primality 8346308408302637 (2 : ZMod 8346308408302637)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (1627, 1), (33329, 1), (125339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (1627, 1), (33329, 1), (125339, 1)] : List FactorBlock).map factorBlockValue).prod) = 8346308408302637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_307
      · exact prime_oneHundredThirtyFourEB_1627
      · exact prime_oneHundredThirtyFourEB_33329
      · exact prime_oneHundredThirtyFourEB_125339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8346308408302637) ^ 4173154204151318 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8346308408302637) ^ 27186672339748 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8346308408302637) ^ 5129876096068 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8346308408302637) ^ 250421807084 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8346308408302637) ^ 66589875524 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_12124737204839807 : Nat.Prime 12124737204839807 := by
  apply lucas_primality 12124737204839807 (5 : ZMod 12124737204839807)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (69283439, 1), (87500977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (69283439, 1), (87500977, 1)] : List FactorBlock).map factorBlockValue).prod) = 12124737204839807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_69283439
      · exact prime_oneHundredThirtyFourEB_87500977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12124737204839807) ^ 6062368602419903 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 12124737204839807) ^ 175001954 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 12124737204839807) ^ 138566878 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_17023647588543677 : Nat.Prime 17023647588543677 := by
  apply lucas_primality 17023647588543677 (2 : ZMod 17023647588543677)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (277, 1), (138401, 1), (111012947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (277, 1), (138401, 1), (111012947, 1)] : List FactorBlock).map factorBlockValue).prod) = 17023647588543677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_277
      · exact prime_oneHundredThirtyFourEB_138401
      · exact prime_oneHundredThirtyFourEB_111012947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17023647588543677) ^ 8511823794271838 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 17023647588543677) ^ 61457211510988 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 17023647588543677) ^ 123002345276 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 17023647588543677) ^ 153348308 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_20289329043582881 : Nat.Prime 20289329043582881 := by
  apply lucas_primality 20289329043582881 (3 : ZMod 20289329043582881)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (67, 1), (2677, 1), (23339, 1), (30293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (67, 1), (2677, 1), (23339, 1), (30293, 1)] : List FactorBlock).map factorBlockValue).prod) = 20289329043582881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_67
      · exact prime_oneHundredThirtyFourEB_2677
      · exact prime_oneHundredThirtyFourEB_23339
      · exact prime_oneHundredThirtyFourEB_30293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20289329043582881) ^ 10144664521791440 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20289329043582881) ^ 4057865808716576 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20289329043582881) ^ 302825806620640 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20289329043582881) ^ 7579129265440 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20289329043582881) ^ 869331549920 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20289329043582881) ^ 669769552160 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_23832424225533169 : Nat.Prime 23832424225533169 := by
  apply lucas_primality 23832424225533169 (19 : ZMod 23832424225533169)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (17, 1), (347, 1), (5591, 1), (716869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (17, 1), (347, 1), (5591, 1), (716869, 1)] : List FactorBlock).map factorBlockValue).prod) = 23832424225533169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_347
      · exact prime_oneHundredThirtyFourEB_5591
      · exact prime_oneHundredThirtyFourEB_716869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 23832424225533169) ^ 11916212112766584 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 23832424225533169) ^ 7944141408511056 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 23832424225533169) ^ 3404632032219024 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 23832424225533169) ^ 1401907307384304 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 23832424225533169) ^ 68681337825744 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 23832424225533169) ^ 4262640712848 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (19 : ZMod 23832424225533169) ^ 33245159472 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_27008388370124849 : Nat.Prime 27008388370124849 := by
  apply lucas_primality 27008388370124849 (3 : ZMod 27008388370124849)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4363213, 1), (386876431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4363213, 1), (386876431, 1)] : List FactorBlock).map factorBlockValue).prod) = 27008388370124849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_4363213
      · exact prime_oneHundredThirtyFourEB_386876431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27008388370124849) ^ 13504194185062424 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27008388370124849) ^ 6190022896 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27008388370124849) ^ 69811408 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_27705412946543701 : Nat.Prime 27705412946543701 := by
  apply lucas_primality 27705412946543701 (2 : ZMod 27705412946543701)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (17, 1), (5432433911087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (17, 1), (5432433911087, 1)] : List FactorBlock).map factorBlockValue).prod) = 27705412946543701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_5432433911087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27705412946543701) ^ 13852706473271850 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27705412946543701) ^ 9235137648847900 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27705412946543701) ^ 5541082589308740 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27705412946543701) ^ 1629730173326100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27705412946543701) ^ 5100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_28325195012496611 : Nat.Prime 28325195012496611 := by
  apply lucas_primality 28325195012496611 (2 : ZMod 28325195012496611)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31139, 1), (90963727199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31139, 1), (90963727199, 1)] : List FactorBlock).map factorBlockValue).prod) = 28325195012496611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_31139
      · exact prime_oneHundredThirtyFourEB_90963727199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28325195012496611) ^ 14162597506248305 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 28325195012496611) ^ 5665039002499322 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 28325195012496611) ^ 909637271990 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 28325195012496611) ^ 311390 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_33704090966624959 : Nat.Prime 33704090966624959 := by
  apply lucas_primality 33704090966624959 (3 : ZMod 33704090966624959)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (1014779, 1), (55914533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (1014779, 1), (55914533, 1)] : List FactorBlock).map factorBlockValue).prod) = 33704090966624959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_1014779
      · exact prime_oneHundredThirtyFourEB_55914533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33704090966624959) ^ 16852045483312479 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 33704090966624959) ^ 11234696988874986 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 33704090966624959) ^ 3064008269693178 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 33704090966624959) ^ 33213232602 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 33704090966624959) ^ 602778726 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_49261164084858547 : Nat.Prime 49261164084858547 := by
  apply lucas_primality 49261164084858547 (2 : ZMod 49261164084858547)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5783, 1), (473237305559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5783, 1), (473237305559, 1)] : List FactorBlock).map factorBlockValue).prod) = 49261164084858547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5783
      · exact prime_oneHundredThirtyFourEB_473237305559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49261164084858547) ^ 24630582042429273 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49261164084858547) ^ 16420388028286182 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49261164084858547) ^ 8518271500062 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49261164084858547) ^ 104094 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_69064820657869891 : Nat.Prime 69064820657869891 := by
  apply lucas_primality 69064820657869891 (7 : ZMod 69064820657869891)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (10359553, 1), (31746553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (10359553, 1), (31746553, 1)] : List FactorBlock).map factorBlockValue).prod) = 69064820657869891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_10359553
      · exact prime_oneHundredThirtyFourEB_31746553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 69064820657869891) ^ 34532410328934945 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69064820657869891) ^ 23021606885956630 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69064820657869891) ^ 13812964131573978 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69064820657869891) ^ 9866402951124270 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69064820657869891) ^ 6666776130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 69064820657869891) ^ 2175506130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_74561406988255949 : Nat.Prime 74561406988255949 := by
  apply lucas_primality 74561406988255949 (2 : ZMod 74561406988255949)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5099, 1), (7883, 1), (463743211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5099, 1), (7883, 1), (463743211, 1)] : List FactorBlock).map factorBlockValue).prod) = 74561406988255949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5099
      · exact prime_oneHundredThirtyFourEB_7883
      · exact prime_oneHundredThirtyFourEB_463743211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74561406988255949) ^ 37280703494127974 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 74561406988255949) ^ 14622750929252 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 74561406988255949) ^ 9458506531556 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 74561406988255949) ^ 160781668 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_79245847210491347 : Nat.Prime 79245847210491347 := by
  apply lucas_primality 79245847210491347 (2 : ZMod 79245847210491347)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (290659, 1), (1770402511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (290659, 1), (1770402511, 1)] : List FactorBlock).map factorBlockValue).prod) = 79245847210491347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_290659
      · exact prime_oneHundredThirtyFourEB_1770402511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79245847210491347) ^ 39622923605245673 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79245847210491347) ^ 11320835315784478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79245847210491347) ^ 7204167928226486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79245847210491347) ^ 272641986694 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79245847210491347) ^ 44761486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_95329696902132677 : Nat.Prime 95329696902132677 := by
  apply lucas_primality 95329696902132677 (2 : ZMod 95329696902132677)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23832424225533169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23832424225533169, 1)] : List FactorBlock).map factorBlockValue).prod) = 95329696902132677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_23832424225533169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 95329696902132677) ^ 47664848451066338 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 95329696902132677) ^ 4 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_136177312639461307 : Nat.Prime 136177312639461307 := by
  apply lucas_primality 136177312639461307 (2 : ZMod 136177312639461307)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (2953, 1), (68016083159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (2953, 1), (68016083159, 1)] : List FactorBlock).map factorBlockValue).prod) = 136177312639461307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_113
      · exact prime_oneHundredThirtyFourEB_2953
      · exact prime_oneHundredThirtyFourEB_68016083159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 136177312639461307) ^ 68088656319730653 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136177312639461307) ^ 45392437546487102 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136177312639461307) ^ 1205108961411162 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136177312639461307) ^ 46114904381802 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136177312639461307) ^ 2002134 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_174120659880621211 : Nat.Prime 174120659880621211 := by
  apply lucas_primality 174120659880621211 (2 : ZMod 174120659880621211)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (52288486450637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (52288486450637, 1)] : List FactorBlock).map factorBlockValue).prod) = 174120659880621211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_37
      · exact prime_oneHundredThirtyFourEB_52288486450637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 174120659880621211) ^ 87060329940310605 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 174120659880621211) ^ 58040219960207070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 174120659880621211) ^ 34824131976124242 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 174120659880621211) ^ 4705963780557330 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 174120659880621211) ^ 3330 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_176741556522303979 : Nat.Prime 176741556522303979 := by
  apply lucas_primality 176741556522303979 (2 : ZMod 176741556522303979)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (200171, 1), (49052936551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (200171, 1), (49052936551, 1)] : List FactorBlock).map factorBlockValue).prod) = 176741556522303979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_200171
      · exact prime_oneHundredThirtyFourEB_49052936551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 176741556522303979) ^ 88370778261151989 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 176741556522303979) ^ 58913852174101326 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 176741556522303979) ^ 882952857918 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 176741556522303979) ^ 3603078 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_277173143132052989 : Nat.Prime 277173143132052989 := by
  apply lucas_primality 277173143132052989 (2 : ZMod 277173143132052989)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3588457, 1), (19310050471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3588457, 1), (19310050471, 1)] : List FactorBlock).map factorBlockValue).prod) = 277173143132052989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3588457
      · exact prime_oneHundredThirtyFourEB_19310050471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 277173143132052989) ^ 138586571566026494 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 277173143132052989) ^ 77240201884 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 277173143132052989) ^ 14353828 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_303935138290121339 : Nat.Prime 303935138290121339 := by
  apply lucas_primality 303935138290121339 (2 : ZMod 303935138290121339)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (4789, 1), (31700929921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (4789, 1), (31700929921, 1)] : List FactorBlock).map factorBlockValue).prod) = 303935138290121339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_4789
      · exact prime_oneHundredThirtyFourEB_31700929921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 303935138290121339) ^ 151967569145060669 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 303935138290121339) ^ 43419305470017334 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 303935138290121339) ^ 27630467117283758 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 303935138290121339) ^ 23379626022317026 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 303935138290121339) ^ 63465261701842 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 303935138290121339) ^ 9587578 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_614435169710353877 : Nat.Prime 614435169710353877 := by
  apply lucas_primality 614435169710353877 (2 : ZMod 614435169710353877)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 3), (4363, 1), (5132985757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 3), (4363, 1), (5132985757, 1)] : List FactorBlock).map factorBlockValue).prod) = 614435169710353877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_4363
      · exact prime_oneHundredThirtyFourEB_5132985757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 614435169710353877) ^ 307217584855176938 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614435169710353877) ^ 32338693142650204 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614435169710353877) ^ 140828597229052 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614435169710353877) ^ 119703268 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1078298171634392227 : Nat.Prime 1078298171634392227 := by
  apply lucas_primality 1078298171634392227 (12 : ZMod 1078298171634392227)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (109, 1), (4618414461467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (109, 1), (4618414461467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1078298171634392227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_109
      · exact prime_oneHundredThirtyFourEB_4618414461467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1078298171634392227) ^ 539149085817196113 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1078298171634392227) ^ 359432723878130742 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1078298171634392227) ^ 154042595947770318 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1078298171634392227) ^ 63429304213787778 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1078298171634392227) ^ 9892643776462314 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1078298171634392227) ^ 233478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1159255302412969301 : Nat.Prime 1159255302412969301 := by
  apply lucas_primality 1159255302412969301 (10 : ZMod 1159255302412969301)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (11, 1), (241, 1), (1021, 1), (87407267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (11, 1), (241, 1), (1021, 1), (87407267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1159255302412969301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_241
      · exact prime_oneHundredThirtyFourEB_1021
      · exact prime_oneHundredThirtyFourEB_87407267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1159255302412969301) ^ 579627651206484650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1159255302412969301) ^ 231851060482593860 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1159255302412969301) ^ 165607900344709900 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1159255302412969301) ^ 105386845673906300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1159255302412969301) ^ 4810187976817300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1159255302412969301) ^ 1135411657603300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1159255302412969301) ^ 13262687900 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1184041154424372983 : Nat.Prime 1184041154424372983 := by
  apply lucas_primality 1184041154424372983 (5 : ZMod 1184041154424372983)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (75859237, 1), (251748353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (75859237, 1), (251748353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184041154424372983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_75859237
      · exact prime_oneHundredThirtyFourEB_251748353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1184041154424372983) ^ 592020577212186491 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184041154424372983) ^ 38194875949173322 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184041154424372983) ^ 15608397886 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184041154424372983) ^ 4703272694 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1545550438306498501 : Nat.Prime 1545550438306498501 := by
  apply lucas_primality 1545550438306498501 (6 : ZMod 1545550438306498501)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (1030366958870999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (1030366958870999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1545550438306498501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_1030366958870999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1545550438306498501) ^ 772775219153249250 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1545550438306498501) ^ 515183479435499500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1545550438306498501) ^ 309110087661299700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1545550438306498501) ^ 1500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1796041496094376301 : Nat.Prime 1796041496094376301 := by
  apply lucas_primality 1796041496094376301 (3 : ZMod 1796041496094376301)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (11, 2), (29, 1), (31, 1), (53, 1), (63576901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (11, 2), (29, 1), (31, 1), (53, 1), (63576901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1796041496094376301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_53
      · exact prime_oneHundredThirtyFourEB_63576901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1796041496094376301) ^ 898020748047188150 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 359208299218875260 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 256577356584910900 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 163276499644943300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 61932465382564700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 57936822454657300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 33887575398007100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796041496094376301) ^ 28249906300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_101
      · exact prime_oneHundredThirtyFourEB_191
      · exact prime_oneHundredThirtyFourEB_48017
      · exact prime_oneHundredThirtyFourEB_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2303515037688301609 : Nat.Prime 2303515037688301609 := by
  apply lucas_primality 2303515037688301609 (11 : ZMod 2303515037688301609)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (157, 1), (611336262656131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (157, 1), (611336262656131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2303515037688301609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_157
      · exact prime_oneHundredThirtyFourEB_611336262656131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2303515037688301609) ^ 1151757518844150804 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2303515037688301609) ^ 767838345896100536 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2303515037688301609) ^ 14672070303747144 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2303515037688301609) ^ 3768 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2389482478878043741 : Nat.Prime 2389482478878043741 := by
  apply lucas_primality 2389482478878043741 (2 : ZMod 2389482478878043741)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (701, 1), (769247, 1), (73853107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (701, 1), (769247, 1), (73853107, 1)] : List FactorBlock).map factorBlockValue).prod) = 2389482478878043741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_701
      · exact prime_oneHundredThirtyFourEB_769247
      · exact prime_oneHundredThirtyFourEB_73853107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2389482478878043741) ^ 1194741239439021870 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389482478878043741) ^ 796494159626014580 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389482478878043741) ^ 477896495775608748 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389482478878043741) ^ 3408676860025740 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389482478878043741) ^ 3106261680420 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389482478878043741) ^ 32354528820 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4140563415844176589 : Nat.Prime 4140563415844176589 := by
  apply lucas_primality 4140563415844176589 (2 : ZMod 4140563415844176589)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (7309, 1), (306529, 1), (6696083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (7309, 1), (306529, 1), (6696083, 1)] : List FactorBlock).map factorBlockValue).prod) = 4140563415844176589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_7309
      · exact prime_oneHundredThirtyFourEB_306529
      · exact prime_oneHundredThirtyFourEB_6696083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4140563415844176589) ^ 2070281707922088294 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4140563415844176589) ^ 1380187805281392196 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4140563415844176589) ^ 180024496341051156 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4140563415844176589) ^ 566502040750332 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4140563415844176589) ^ 13507901098572 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4140563415844176589) ^ 618356047236 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4841395922102438087 : Nat.Prime 4841395922102438087 := by
  apply lucas_primality 4841395922102438087 (5 : ZMod 4841395922102438087)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1567, 1), (3343, 1), (462099215603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1567, 1), (3343, 1), (462099215603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4841395922102438087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1567
      · exact prime_oneHundredThirtyFourEB_3343
      · exact prime_oneHundredThirtyFourEB_462099215603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4841395922102438087) ^ 2420697961051219043 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4841395922102438087) ^ 3089595355521658 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4841395922102438087) ^ 1448218941699802 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4841395922102438087) ^ 10476962 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4846640317853230951 : Nat.Prime 4846640317853230951 := by
  apply lucas_primality 4846640317853230951 (3 : ZMod 4846640317853230951)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (281, 1), (311, 1), (463, 1), (27536189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (281, 1), (311, 1), (463, 1), (27536189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4846640317853230951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_281
      · exact prime_oneHundredThirtyFourEB_311
      · exact prime_oneHundredThirtyFourEB_463
      · exact prime_oneHundredThirtyFourEB_27536189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4846640317853230951) ^ 2423320158926615475 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 1615546772617743650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 969328063570646190 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 167125528201835550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 17247830312644950 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 15584052468981450 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 10467905654110650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4846640317853230951) ^ 176009843550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_5330197951516363747 : Nat.Prime 5330197951516363747 := by
  apply lucas_primality 5330197951516363747 (2 : ZMod 5330197951516363747)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (37, 1), (1263678983289797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (37, 1), (1263678983289797, 1)] : List FactorBlock).map factorBlockValue).prod) = 5330197951516363747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_37
      · exact prime_oneHundredThirtyFourEB_1263678983289797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5330197951516363747) ^ 2665098975758181873 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5330197951516363747) ^ 1776732650505454582 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5330197951516363747) ^ 280536734290334934 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5330197951516363747) ^ 144059404095036858 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5330197951516363747) ^ 4218 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_6004941342649281533 : Nat.Prime 6004941342649281533 := by
  apply lucas_primality 6004941342649281533 (2 : ZMod 6004941342649281533)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (28325195012496611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (28325195012496611, 1)] : List FactorBlock).map factorBlockValue).prod) = 6004941342649281533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_53
      · exact prime_oneHundredThirtyFourEB_28325195012496611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6004941342649281533) ^ 3002470671324640766 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6004941342649281533) ^ 113300780049986444 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6004941342649281533) ^ 212 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_8181213754688881897 : Nat.Prime 8181213754688881897 := by
  apply lucas_primality 8181213754688881897 (5 : ZMod 8181213754688881897)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (29, 1), (2205803, 1), (484450147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (29, 1), (2205803, 1), (484450147, 1)] : List FactorBlock).map factorBlockValue).prod) = 8181213754688881897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_2205803
      · exact prime_oneHundredThirtyFourEB_484450147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8181213754688881897) ^ 4090606877344440948 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8181213754688881897) ^ 2727071251562960632 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8181213754688881897) ^ 743746704971716536 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8181213754688881897) ^ 282110819127202824 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8181213754688881897) ^ 3708950325432 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8181213754688881897) ^ 16887627768 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_11564757900185713577 : Nat.Prime 11564757900185713577 := by
  apply lucas_primality 11564757900185713577 (5 : ZMod 11564757900185713577)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (47, 1), (547, 1), (1045859, 1), (1311307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (47, 1), (547, 1), (1045859, 1), (1311307, 1)] : List FactorBlock).map factorBlockValue).prod) = 11564757900185713577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_547
      · exact prime_oneHundredThirtyFourEB_1045859
      · exact prime_oneHundredThirtyFourEB_1311307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11564757900185713577) ^ 5782378950092856788 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11564757900185713577) ^ 282067265858188136 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11564757900185713577) ^ 246058678727355608 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11564757900185713577) ^ 21142153382423608 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11564757900185713577) ^ 11057664465464 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11564757900185713577) ^ 8819260402168 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_11848555844366480563 : Nat.Prime 11848555844366480563 := by
  apply lucas_primality 11848555844366480563 (3 : ZMod 11848555844366480563)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22409, 1), (295901, 1), (297814103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22409, 1), (295901, 1), (297814103, 1)] : List FactorBlock).map factorBlockValue).prod) = 11848555844366480563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_22409
      · exact prime_oneHundredThirtyFourEB_295901
      · exact prime_oneHundredThirtyFourEB_297814103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11848555844366480563) ^ 5924277922183240281 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11848555844366480563) ^ 3949518614788826854 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11848555844366480563) ^ 528740945350818 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11848555844366480563) ^ 40042297404762 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11848555844366480563) ^ 39785073054 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_14369534014660027429 : Nat.Prime 14369534014660027429 := by
  apply lucas_primality 14369534014660027429 (2 : ZMod 14369534014660027429)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (71, 1), (361549, 1), (1504784231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (71, 1), (361549, 1), (1504784231, 1)] : List FactorBlock).map factorBlockValue).prod) = 14369534014660027429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_71
      · exact prime_oneHundredThirtyFourEB_361549
      · exact prime_oneHundredThirtyFourEB_1504784231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14369534014660027429) ^ 7184767007330013714 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369534014660027429) ^ 4789844671553342476 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369534014660027429) ^ 463533355311613788 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369534014660027429) ^ 202387803023380668 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369534014660027429) ^ 39744361109172 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369534014660027429) ^ 9549232188 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_16562253663376706357 : Nat.Prime 16562253663376706357 := by
  apply lucas_primality 16562253663376706357 (2 : ZMod 16562253663376706357)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4140563415844176589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4140563415844176589, 1)] : List FactorBlock).map factorBlockValue).prod) = 16562253663376706357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_4140563415844176589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 16562253663376706357) ^ 8281126831688353178 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16562253663376706357) ^ 4 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_40126678528925220503 : Nat.Prime 40126678528925220503 := by
  apply lucas_primality 40126678528925220503 (5 : ZMod 40126678528925220503)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (223, 1), (3102418318302553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (223, 1), (3102418318302553, 1)] : List FactorBlock).map factorBlockValue).prod) = 40126678528925220503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_223
      · exact prime_oneHundredThirtyFourEB_3102418318302553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40126678528925220503) ^ 20063339264462610251 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 40126678528925220503) ^ 1383678569962938638 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 40126678528925220503) ^ 179940262461548074 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 40126678528925220503) ^ 12934 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_56070178055168473649 : Nat.Prime 56070178055168473649 := by
  apply lucas_primality 56070178055168473649 (3 : ZMod 56070178055168473649)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47, 1), (74561406988255949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47, 1), (74561406988255949, 1)] : List FactorBlock).map factorBlockValue).prod) = 56070178055168473649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_74561406988255949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56070178055168473649) ^ 28035089027584236824 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 56070178055168473649) ^ 1192982511812095184 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 56070178055168473649) ^ 752 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_57539928849277628261 : Nat.Prime 57539928849277628261 := by
  apply lucas_primality 57539928849277628261 (2 : ZMod 57539928849277628261)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 2), (17023647588543677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 2), (17023647588543677, 1)] : List FactorBlock).map factorBlockValue).prod) = 57539928849277628261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_17023647588543677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57539928849277628261) ^ 28769964424638814130 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57539928849277628261) ^ 11507985769855525652 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57539928849277628261) ^ 4426148373021356020 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57539928849277628261) ^ 3380 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_71554509335218156517 : Nat.Prime 71554509335218156517 := by
  apply lucas_primality 71554509335218156517 (2 : ZMod 71554509335218156517)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (461, 1), (256979893031339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (461, 1), (256979893031339, 1)] : List FactorBlock).map factorBlockValue).prod) = 71554509335218156517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_151
      · exact prime_oneHundredThirtyFourEB_461
      · exact prime_oneHundredThirtyFourEB_256979893031339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71554509335218156517) ^ 35777254667609078258 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 71554509335218156517) ^ 473870922749789116 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 71554509335218156517) ^ 155215855390928756 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 71554509335218156517) ^ 278444 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_73639134911939129341 : Nat.Prime 73639134911939129341 := by
  apply lucas_primality 73639134911939129341 (6 : ZMod 73639134911939129341)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (8753, 1), (140216944498913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (8753, 1), (140216944498913, 1)] : List FactorBlock).map factorBlockValue).prod) = 73639134911939129341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_8753
      · exact prime_oneHundredThirtyFourEB_140216944498913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 73639134911939129341) ^ 36819567455969564670 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 73639134911939129341) ^ 24546378303979709780 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 73639134911939129341) ^ 14727826982387825868 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 73639134911939129341) ^ 8413016669934780 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 73639134911939129341) ^ 525180 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_94932219019526981201 : Nat.Prime 94932219019526981201 := by
  apply lucas_primality 94932219019526981201 (6 : ZMod 94932219019526981201)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (67, 1), (1019, 1), (5657, 1), (614495173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (67, 1), (1019, 1), (5657, 1), (614495173, 1)] : List FactorBlock).map factorBlockValue).prod) = 94932219019526981201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_67
      · exact prime_oneHundredThirtyFourEB_1019
      · exact prime_oneHundredThirtyFourEB_5657
      · exact prime_oneHundredThirtyFourEB_614495173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 94932219019526981201) ^ 47466109509763490600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94932219019526981201) ^ 18986443803905396240 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94932219019526981201) ^ 1416898791336223600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94932219019526981201) ^ 93162138390114800 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94932219019526981201) ^ 16781371578491600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94932219019526981201) ^ 154488144400 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_116762258000298777577 : Nat.Prime 116762258000298777577 := by
  apply lucas_primality 116762258000298777577 (5 : ZMod 116762258000298777577)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (509, 1), (14438527, 1), (661988693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (509, 1), (14438527, 1), (661988693, 1)] : List FactorBlock).map factorBlockValue).prod) = 116762258000298777577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_509
      · exact prime_oneHundredThirtyFourEB_14438527
      · exact prime_oneHundredThirtyFourEB_661988693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 116762258000298777577) ^ 58381129000149388788 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 116762258000298777577) ^ 38920752666766259192 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 116762258000298777577) ^ 229395398821805064 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 116762258000298777577) ^ 8086853873688 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 116762258000298777577) ^ 176381045832 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_136619840590887082229 : Nat.Prime 136619840590887082229 := by
  apply lucas_primality 136619840590887082229 (2 : ZMod 136619840590887082229)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (431, 1), (79245847210491347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (431, 1), (79245847210491347, 1)] : List FactorBlock).map factorBlockValue).prod) = 136619840590887082229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_431
      · exact prime_oneHundredThirtyFourEB_79245847210491347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 136619840590887082229) ^ 68309920295443541114 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136619840590887082229) ^ 316983388841965388 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136619840590887082229) ^ 1724 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_194565954597662587501 : Nat.Prime 194565954597662587501 := by
  apply lucas_primality 194565954597662587501 (2 : ZMod 194565954597662587501)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 5), (11, 1), (117053, 1), (1343195081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 5), (11, 1), (117053, 1), (1343195081, 1)] : List FactorBlock).map factorBlockValue).prod) = 194565954597662587501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_117053
      · exact prime_oneHundredThirtyFourEB_1343195081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 194565954597662587501) ^ 97282977298831293750 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 194565954597662587501) ^ 64855318199220862500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 194565954597662587501) ^ 38913190919532517500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 194565954597662587501) ^ 17687814054332962500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 194565954597662587501) ^ 1662203912737500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 194565954597662587501) ^ 144853087500 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_247423773590156346803 : Nat.Prime 247423773590156346803 := by
  apply lucas_primality 247423773590156346803 (2 : ZMod 247423773590156346803)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6917, 1), (26821, 1), (666835464193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6917, 1), (26821, 1), (666835464193, 1)] : List FactorBlock).map factorBlockValue).prod) = 247423773590156346803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_6917
      · exact prime_oneHundredThirtyFourEB_26821
      · exact prime_oneHundredThirtyFourEB_666835464193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247423773590156346803) ^ 123711886795078173401 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 247423773590156346803) ^ 35770387970240906 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 247423773590156346803) ^ 9225001811645962 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 247423773590156346803) ^ 371041714 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_364778451972780348059 : Nat.Prime 364778451972780348059 := by
  apply lucas_primality 364778451972780348059 (2 : ZMod 364778451972780348059)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (877, 1), (2505656276001019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (877, 1), (2505656276001019, 1)] : List FactorBlock).map factorBlockValue).prod) = 364778451972780348059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_83
      · exact prime_oneHundredThirtyFourEB_877
      · exact prime_oneHundredThirtyFourEB_2505656276001019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 364778451972780348059) ^ 182389225986390174029 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 364778451972780348059) ^ 4394921108105787326 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 364778451972780348059) ^ 415938941816169154 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 364778451972780348059) ^ 145582 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_443104856894482114231 : Nat.Prime 443104856894482114231 := by
  apply lucas_primality 443104856894482114231 (3 : ZMod 443104856894482114231)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (89, 1), (161986459, 1), (341503597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (89, 1), (161986459, 1), (341503597, 1)] : List FactorBlock).map factorBlockValue).prod) = 443104856894482114231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_89
      · exact prime_oneHundredThirtyFourEB_161986459
      · exact prime_oneHundredThirtyFourEB_341503597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 443104856894482114231) ^ 221552428447241057115 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 443104856894482114231) ^ 147701618964827371410 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 443104856894482114231) ^ 88620971378896422846 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 443104856894482114231) ^ 4978706257241372070 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 443104856894482114231) ^ 2735443811970 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 443104856894482114231) ^ 1297511536590 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_990173207880485302643 : Nat.Prime 990173207880485302643 := by
  apply lucas_primality 990173207880485302643 (2 : ZMod 990173207880485302643)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (49871, 1), (85411, 1), (116230282141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (49871, 1), (85411, 1), (116230282141, 1)] : List FactorBlock).map factorBlockValue).prod) = 990173207880485302643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_49871
      · exact prime_oneHundredThirtyFourEB_85411
      · exact prime_oneHundredThirtyFourEB_116230282141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 990173207880485302643) ^ 495086603940242651321 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 990173207880485302643) ^ 19854689255889902 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 990173207880485302643) ^ 11593040801307622 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 990173207880485302643) ^ 8519063962 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1083229461715149289273 : Nat.Prime 1083229461715149289273 := by
  apply lucas_primality 1083229461715149289273 (5 : ZMod 1083229461715149289273)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2657, 1), (11171, 1), (1520637217199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2657, 1), (11171, 1), (1520637217199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1083229461715149289273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_2657
      · exact prime_oneHundredThirtyFourEB_11171
      · exact prime_oneHundredThirtyFourEB_1520637217199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1083229461715149289273) ^ 541614730857574644636 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1083229461715149289273) ^ 361076487238383096424 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1083229461715149289273) ^ 407688920479920696 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1083229461715149289273) ^ 96967994066345832 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1083229461715149289273) ^ 712352328 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1612908689563462156153 : Nat.Prime 1612908689563462156153 := by
  apply lucas_primality 1612908689563462156153 (5 : ZMod 1612908689563462156153)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 2), (5021, 1), (6616258056431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 2), (5021, 1), (6616258056431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1612908689563462156153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_5021
      · exact prime_oneHundredThirtyFourEB_6616258056431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1612908689563462156153) ^ 806454344781731078076 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1612908689563462156153) ^ 537636229854487385384 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1612908689563462156153) ^ 230415527080494593736 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1612908689563462156153) ^ 94876981739027185656 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1612908689563462156153) ^ 321232561155837912 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1612908689563462156153) ^ 243779592 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1713934325891930117351 : Nat.Prime 1713934325891930117351 := by
  apply lucas_primality 1713934325891930117351 (31 : ZMod 1713934325891930117351)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (257, 1), (47741, 1), (247991, 1), (592939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (257, 1), (47741, 1), (247991, 1), (592939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1713934325891930117351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_257
      · exact prime_oneHundredThirtyFourEB_47741
      · exact prime_oneHundredThirtyFourEB_247991
      · exact prime_oneHundredThirtyFourEB_592939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1713934325891930117351) ^ 856967162945965058675 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1713934325891930117351) ^ 342786865178386023470 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1713934325891930117351) ^ 90207069783785795650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1713934325891930117351) ^ 6669005159112568550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1713934325891930117351) ^ 35900679204288350 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1713934325891930117351) ^ 6911276320075850 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (31 : ZMod 1713934325891930117351) ^ 2890574453513650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2414081714462884608073 : Nat.Prime 2414081714462884608073 := by
  apply lucas_primality 2414081714462884608073 (5 : ZMod 2414081714462884608073)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (14369534014660027429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (14369534014660027429, 1)] : List FactorBlock).map factorBlockValue).prod) = 2414081714462884608073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_14369534014660027429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2414081714462884608073) ^ 1207040857231442304036 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2414081714462884608073) ^ 804693904820961536024 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2414081714462884608073) ^ 344868816351840658296 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2414081714462884608073) ^ 168 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3422962295649460455181 : Nat.Prime 3422962295649460455181 := by
  apply lucas_primality 3422962295649460455181 (6 : ZMod 3422962295649460455181)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (818399, 1), (69708505990547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (818399, 1), (69708505990547, 1)] : List FactorBlock).map factorBlockValue).prod) = 3422962295649460455181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_818399
      · exact prime_oneHundredThirtyFourEB_69708505990547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3422962295649460455181) ^ 1711481147824730227590 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3422962295649460455181) ^ 1140987431883153485060 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3422962295649460455181) ^ 684592459129892091036 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3422962295649460455181) ^ 4182510359432820 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3422962295649460455181) ^ 49103940 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_4241998711787324733503 : Nat.Prime 4241998711787324733503 := by
  apply lucas_primality 4241998711787324733503 (5 : ZMod 4241998711787324733503)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1493149367, 1), (83558062409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1493149367, 1), (83558062409, 1)] : List FactorBlock).map factorBlockValue).prod) = 4241998711787324733503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_1493149367
      · exact prime_oneHundredThirtyFourEB_83558062409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4241998711787324733503) ^ 2120999355893662366751 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4241998711787324733503) ^ 249529335987489690206 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4241998711787324733503) ^ 2840974121906 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4241998711787324733503) ^ 50767078478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_7724715018069084836417 : Nat.Prime 7724715018069084836417 := by
  apply lucas_primality 7724715018069084836417 (3 : ZMod 7724715018069084836417)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (11, 1), (167, 1), (191, 1), (653, 1), (79397, 1), (947861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (11, 1), (167, 1), (191, 1), (653, 1), (79397, 1), (947861, 1)] : List FactorBlock).map factorBlockValue).prod) = 7724715018069084836417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_167
      · exact prime_oneHundredThirtyFourEB_191
      · exact prime_oneHundredThirtyFourEB_653
      · exact prime_oneHundredThirtyFourEB_79397
      · exact prime_oneHundredThirtyFourEB_947861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7724715018069084836417) ^ 3862357509034542418208 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 1103530716867012119488 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 702246819824462257856 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 46255778551311885248 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 40443534126016150976 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 11829578894439639872 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 97292278273348928 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7724715018069084836417) ^ 8149628498344256 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_9331678846476983502283 : Nat.Prime 9331678846476983502283 := by
  apply lucas_primality 9331678846476983502283 (2 : ZMod 9331678846476983502283)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (6004941342649281533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (6004941342649281533, 1)] : List FactorBlock).map factorBlockValue).prod) = 9331678846476983502283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_37
      · exact prime_oneHundredThirtyFourEB_6004941342649281533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9331678846476983502283) ^ 4665839423238491751141 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9331678846476983502283) ^ 3110559615492327834094 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9331678846476983502283) ^ 1333096978068140500326 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9331678846476983502283) ^ 252207536391269824386 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9331678846476983502283) ^ 1554 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_10375570929036120779107 : Nat.Prime 10375570929036120779107 := by
  apply lucas_primality 10375570929036120779107 (3 : ZMod 10375570929036120779107)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1483, 1), (191489017, 1), (2029805747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1483, 1), (191489017, 1), (2029805747, 1)] : List FactorBlock).map factorBlockValue).prod) = 10375570929036120779107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1483
      · exact prime_oneHundredThirtyFourEB_191489017
      · exact prime_oneHundredThirtyFourEB_2029805747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10375570929036120779107) ^ 5187785464518060389553 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10375570929036120779107) ^ 3458523643012040259702 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10375570929036120779107) ^ 6996339129491652582 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10375570929036120779107) ^ 54183634610418 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 10375570929036120779107) ^ 5111607819798 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_10460285366458381854769 : Nat.Prime 10460285366458381854769 := by
  apply lucas_primality 10460285366458381854769 (7 : ZMod 10460285366458381854769)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (47, 1), (1545550438306498501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (47, 1), (1545550438306498501, 1)] : List FactorBlock).map factorBlockValue).prod) = 10460285366458381854769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_47
      · exact prime_oneHundredThirtyFourEB_1545550438306498501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10460285366458381854769) ^ 5230142683229190927384 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10460285366458381854769) ^ 3486761788819460618256 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10460285366458381854769) ^ 222559263116135784144 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10460285366458381854769) ^ 6768 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_13749102838085048122151 : Nat.Prime 13749102838085048122151 := by
  apply lucas_primality 13749102838085048122151 (7 : ZMod 13749102838085048122151)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (11, 1), (17, 1), (43, 1), (4885356419096789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (11, 1), (17, 1), (43, 1), (4885356419096789, 1)] : List FactorBlock).map factorBlockValue).prod) = 13749102838085048122151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_4885356419096789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13749102838085048122151) ^ 6874551419042524061075 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749102838085048122151) ^ 2749820567617009624430 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749102838085048122151) ^ 1964157548297864017450 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749102838085048122151) ^ 1249918439825913465650 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749102838085048122151) ^ 808770755181473418950 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749102838085048122151) ^ 319746577629884840050 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749102838085048122151) ^ 2814350 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_18610403989568248797703 : Nat.Prime 18610403989568248797703 := by
  apply lucas_primality 18610403989568248797703 (3 : ZMod 18610403989568248797703)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (443104856894482114231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (443104856894482114231, 1)] : List FactorBlock).map factorBlockValue).prod) = 18610403989568248797703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_443104856894482114231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18610403989568248797703) ^ 9305201994784124398851 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18610403989568248797703) ^ 6203467996522749599234 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18610403989568248797703) ^ 2658629141366892685386 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18610403989568248797703) ^ 42 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_24468414990305722091699 : Nat.Prime 24468414990305722091699 := by
  apply lucas_primality 24468414990305722091699 (2 : ZMod 24468414990305722091699)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 2), (4841395922102438087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 2), (4841395922102438087, 1)] : List FactorBlock).map factorBlockValue).prod) = 24468414990305722091699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_4841395922102438087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24468414990305722091699) ^ 12234207495152861045849 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 24468414990305722091699) ^ 3495487855757960298814 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 24468414990305722091699) ^ 1287811315279248531142 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 24468414990305722091699) ^ 5054 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_24772694963418564050723 : Nat.Prime 24772694963418564050723 := by
  apply lucas_primality 24772694963418564050723 (2 : ZMod 24772694963418564050723)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1667, 1), (110729, 1), (67103671346627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1667, 1), (110729, 1), (67103671346627, 1)] : List FactorBlock).map factorBlockValue).prod) = 24772694963418564050723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_1667
      · exact prime_oneHundredThirtyFourEB_110729
      · exact prime_oneHundredThirtyFourEB_67103671346627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24772694963418564050723) ^ 12386347481709282025361 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 24772694963418564050723) ^ 14860644849081322166 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 24772694963418564050723) ^ 223723640269654418 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 24772694963418564050723) ^ 369170486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_116268944973390738840349 : Nat.Prime 116268944973390738840349 := by
  apply lucas_primality 116268944973390738840349 (2 : ZMod 116268944973390738840349)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (449, 1), (2009243, 1), (1193331682783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (449, 1), (2009243, 1), (1193331682783, 1)] : List FactorBlock).map factorBlockValue).prod) = 116268944973390738840349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_449
      · exact prime_oneHundredThirtyFourEB_2009243
      · exact prime_oneHundredThirtyFourEB_1193331682783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116268944973390738840349) ^ 58134472486695369420174 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116268944973390738840349) ^ 38756314991130246280116 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116268944973390738840349) ^ 258950879673476033052 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116268944973390738840349) ^ 57867039961513236 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 116268944973390738840349) ^ 97432211556 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_119782248627155194009459 : Nat.Prime 119782248627155194009459 := by
  apply lucas_primality 119782248627155194009459 (2 : ZMod 119782248627155194009459)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (31, 1), (71554509335218156517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (31, 1), (71554509335218156517, 1)] : List FactorBlock).map factorBlockValue).prod) = 119782248627155194009459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_31
      · exact prime_oneHundredThirtyFourEB_71554509335218156517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119782248627155194009459) ^ 59891124313577597004729 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 119782248627155194009459) ^ 39927416209051731336486 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 119782248627155194009459) ^ 3863943504101780451918 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 119782248627155194009459) ^ 1674 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_156140365760890936235021 : Nat.Prime 156140365760890936235021 := by
  apply lucas_primality 156140365760890936235021 (2 : ZMod 156140365760890936235021)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (233, 1), (35393, 1), (132523, 1), (1020522539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (233, 1), (35393, 1), (132523, 1), (1020522539, 1)] : List FactorBlock).map factorBlockValue).prod) = 156140365760890936235021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_233
      · exact prime_oneHundredThirtyFourEB_35393
      · exact prime_oneHundredThirtyFourEB_132523
      · exact prime_oneHundredThirtyFourEB_1020522539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156140365760890936235021) ^ 78070182880445468117510 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156140365760890936235021) ^ 31228073152178187247004 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156140365760890936235021) ^ 22305766537270133747860 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156140365760890936235021) ^ 670130325154038352940 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156140365760890936235021) ^ 4411617149178960140 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156140365760890936235021) ^ 1178213334748616740 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156140365760890936235021) ^ 153000408902180 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_215664010027114871895901 : Nat.Prime 215664010027114871895901 := by
  apply lucas_primality 215664010027114871895901 (2 : ZMod 215664010027114871895901)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (5279, 1), (136177312639461307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (5279, 1), (136177312639461307, 1)] : List FactorBlock).map factorBlockValue).prod) = 215664010027114871895901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_5279
      · exact prime_oneHundredThirtyFourEB_136177312639461307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215664010027114871895901) ^ 107832005013557435947950 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215664010027114871895901) ^ 71888003342371623965300 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215664010027114871895901) ^ 43132802005422974379180 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215664010027114871895901) ^ 40853193791838392100 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215664010027114871895901) ^ 1583700 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_242049414783239683559491 : Nat.Prime 242049414783239683559491 := by
  apply lucas_primality 242049414783239683559491 (13 : ZMod 242049414783239683559491)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (151, 1), (46802383, 1), (1141662848551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (151, 1), (46802383, 1), (1141662848551, 1)] : List FactorBlock).map factorBlockValue).prod) = 242049414783239683559491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_151
      · exact prime_oneHundredThirtyFourEB_46802383
      · exact prime_oneHundredThirtyFourEB_1141662848551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 242049414783239683559491) ^ 121024707391619841779745 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 242049414783239683559491) ^ 80683138261079894519830 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 242049414783239683559491) ^ 48409882956647936711898 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 242049414783239683559491) ^ 1602976256842646910990 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 242049414783239683559491) ^ 5171732703936030 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (13 : ZMod 242049414783239683559491) ^ 212014794990 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_289519755242241258210551 : Nat.Prime 289519755242241258210551 := by
  apply lucas_primality 289519755242241258210551 (11 : ZMod 289519755242241258210551)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (919, 1), (29629, 1), (212655046437161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (919, 1), (29629, 1), (212655046437161, 1)] : List FactorBlock).map factorBlockValue).prod) = 289519755242241258210551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_919
      · exact prime_oneHundredThirtyFourEB_29629
      · exact prime_oneHundredThirtyFourEB_212655046437161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 289519755242241258210551) ^ 144759877621120629105275 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 289519755242241258210551) ^ 57903951048448251642110 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 289519755242241258210551) ^ 315037818544332163450 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 289519755242241258210551) ^ 9771499383787547950 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (11 : ZMod 289519755242241258210551) ^ 1361452550 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_312280731521781872470043 : Nat.Prime 312280731521781872470043 := by
  apply lucas_primality 312280731521781872470043 (2 : ZMod 312280731521781872470043)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (156140365760890936235021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (156140365760890936235021, 1)] : List FactorBlock).map factorBlockValue).prod) = 312280731521781872470043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_156140365760890936235021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 312280731521781872470043) ^ 156140365760890936235021 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 312280731521781872470043) ^ 2 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_754176207356771835393943 : Nat.Prime 754176207356771835393943 := by
  apply lucas_primality 754176207356771835393943 (5 : ZMod 754176207356771835393943)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (72977, 1), (65374219, 1), (26346871739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (72977, 1), (65374219, 1), (26346871739, 1)] : List FactorBlock).map factorBlockValue).prod) = 754176207356771835393943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_72977
      · exact prime_oneHundredThirtyFourEB_65374219
      · exact prime_oneHundredThirtyFourEB_26346871739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 754176207356771835393943) ^ 377088103678385917696971 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 754176207356771835393943) ^ 251392069118923945131314 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 754176207356771835393943) ^ 10334436978181781046 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 754176207356771835393943) ^ 11536293953382018 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 754176207356771835393943) ^ 28624886279778 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1293984060162689231375407 : Nat.Prime 1293984060162689231375407 := by
  apply lucas_primality 1293984060162689231375407 (3 : ZMod 1293984060162689231375407)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (215664010027114871895901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (215664010027114871895901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1293984060162689231375407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_215664010027114871895901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1293984060162689231375407) ^ 646992030081344615687703 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1293984060162689231375407) ^ 431328020054229743791802 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1293984060162689231375407) ^ 6 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_2485936518795163904194741 : Nat.Prime 2485936518795163904194741 := by
  apply lucas_primality 2485936518795163904194741 (2 : ZMod 2485936518795163904194741)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (9661502681, 1), (225704648761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (9661502681, 1), (225704648761, 1)] : List FactorBlock).map factorBlockValue).prod) = 2485936518795163904194741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_9661502681
      · exact prime_oneHundredThirtyFourEB_225704648761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2485936518795163904194741) ^ 1242968259397581952097370 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2485936518795163904194741) ^ 828645506265054634731580 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2485936518795163904194741) ^ 497187303759032780838948 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2485936518795163904194741) ^ 130838764147113889694460 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2485936518795163904194741) ^ 257303299587540 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2485936518795163904194741) ^ 11014113056340 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_5530783496361479028296413 : Nat.Prime 5530783496361479028296413 := by
  apply lucas_primality 5530783496361479028296413 (2 : ZMod 5530783496361479028296413)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (1749383, 1), (3174259426480409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (1749383, 1), (3174259426480409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5530783496361479028296413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_83
      · exact prime_oneHundredThirtyFourEB_1749383
      · exact prime_oneHundredThirtyFourEB_3174259426480409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5530783496361479028296413) ^ 2765391748180739514148206 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5530783496361479028296413) ^ 1843594498787159676098804 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5530783496361479028296413) ^ 66635945739294928051764 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5530783496361479028296413) ^ 3161562388774487364 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5530783496361479028296413) ^ 1742385468 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_5806471282428463762150801 : Nat.Prime 5806471282428463762150801 := by
  apply lucas_primality 5806471282428463762150801 (7 : ZMod 5806471282428463762150801)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (1612908689563462156153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (1612908689563462156153, 1)] : List FactorBlock).map factorBlockValue).prod) = 5806471282428463762150801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_1612908689563462156153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5806471282428463762150801) ^ 2903235641214231881075400 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5806471282428463762150801) ^ 1935490427476154587383600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5806471282428463762150801) ^ 1161294256485692752430160 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5806471282428463762150801) ^ 3600 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_12534517166688678320003359 : Nat.Prime 12534517166688678320003359 := by
  apply lucas_primality 12534517166688678320003359 (3 : ZMod 12534517166688678320003359)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (83, 1), (364778451972780348059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (83, 1), (364778451972780348059, 1)] : List FactorBlock).map factorBlockValue).prod) = 12534517166688678320003359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_83
      · exact prime_oneHundredThirtyFourEB_364778451972780348059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12534517166688678320003359) ^ 6267258583344339160001679 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12534517166688678320003359) ^ 4178172388896226106667786 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12534517166688678320003359) ^ 544979007247333840000146 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12534517166688678320003359) ^ 151018279116731064096426 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12534517166688678320003359) ^ 34362 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_54893888589666737798517829 : Nat.Prime 54893888589666737798517829 := by
  apply lucas_primality 54893888589666737798517829 (2 : ZMod 54893888589666737798517829)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (157, 1), (1713934325891930117351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (157, 1), (1713934325891930117351, 1)] : List FactorBlock).map factorBlockValue).prod) = 54893888589666737798517829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_17
      · exact prime_oneHundredThirtyFourEB_157
      · exact prime_oneHundredThirtyFourEB_1713934325891930117351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54893888589666737798517829) ^ 27446944294833368899258914 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54893888589666737798517829) ^ 18297962863222245932839276 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54893888589666737798517829) ^ 3229052269980396341089284 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54893888589666737798517829) ^ 349642602481953743939604 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 54893888589666737798517829) ^ 32028 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_96482193952361878980829753 : Nat.Prime 96482193952361878980829753 := by
  apply lucas_primality 96482193952361878980829753 (7 : ZMod 96482193952361878980829753)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1202437, 1), (303935138290121339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1202437, 1), (303935138290121339, 1)] : List FactorBlock).map factorBlockValue).prod) = 96482193952361878980829753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_1202437
      · exact prime_oneHundredThirtyFourEB_303935138290121339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 96482193952361878980829753) ^ 48241096976180939490414876 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 96482193952361878980829753) ^ 32160731317453959660276584 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 96482193952361878980829753) ^ 8771108541123807180075432 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 96482193952361878980829753) ^ 80238876508592033496 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 96482193952361878980829753) ^ 317443368 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_169982577757272752453350273 : Nat.Prime 169982577757272752453350273 := by
  apply lucas_primality 169982577757272752453350273 (5 : ZMod 169982577757272752453350273)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (3472651057, 1), (127471190063069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (3472651057, 1), (127471190063069, 1)] : List FactorBlock).map factorBlockValue).prod) = 169982577757272752453350273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_3472651057
      · exact prime_oneHundredThirtyFourEB_127471190063069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 169982577757272752453350273) ^ 84991288878636376226675136 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169982577757272752453350273) ^ 56660859252424250817783424 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169982577757272752453350273) ^ 48948936984218496 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169982577757272752453350273) ^ 1333498005888 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_176222205194414021453306401 : Nat.Prime 176222205194414021453306401 := by
  apply lucas_primality 176222205194414021453306401 (14 : ZMod 176222205194414021453306401)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (25997, 1), (152655731, 1), (18501759973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (25997, 1), (152655731, 1), (18501759973, 1)] : List FactorBlock).map factorBlockValue).prod) = 176222205194414021453306401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_25997
      · exact prime_oneHundredThirtyFourEB_152655731
      · exact prime_oneHundredThirtyFourEB_18501759973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 176222205194414021453306401) ^ 88111102597207010726653200 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 176222205194414021453306401) ^ 58740735064804673817768800 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 176222205194414021453306401) ^ 35244441038882804290661280 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 176222205194414021453306401) ^ 6778559264315652631200 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 176222205194414021453306401) ^ 1154376609643394400 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (14 : ZMod 176222205194414021453306401) ^ 9524618493136800 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_197289866089387553283340541 : Nat.Prime 197289866089387553283340541 := by
  apply lucas_primality 197289866089387553283340541 (2 : ZMod 197289866089387553283340541)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (443, 1), (374531, 1), (1334393, 1), (44555316283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (443, 1), (374531, 1), (1334393, 1), (44555316283, 1)] : List FactorBlock).map factorBlockValue).prod) = 197289866089387553283340541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_443
      · exact prime_oneHundredThirtyFourEB_374531
      · exact prime_oneHundredThirtyFourEB_1334393
      · exact prime_oneHundredThirtyFourEB_44555316283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 197289866089387553283340541) ^ 98644933044693776641670270 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 197289866089387553283340541) ^ 39457973217877510656668108 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 197289866089387553283340541) ^ 445349584851890639465780 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 197289866089387553283340541) ^ 526765117144876000340 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 197289866089387553283340541) ^ 147849895862304098780 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 197289866089387553283340541) ^ 4427975885891380 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_253073102986866142630227563 : Nat.Prime 253073102986866142630227563 := by
  apply lucas_primality 253073102986866142630227563 (2 : ZMod 253073102986866142630227563)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (16339, 1), (40126678528925220503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (16339, 1), (40126678528925220503, 1)] : List FactorBlock).map factorBlockValue).prod) = 253073102986866142630227563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_193
      · exact prime_oneHundredThirtyFourEB_16339
      · exact prime_oneHundredThirtyFourEB_40126678528925220503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 253073102986866142630227563) ^ 126536551493433071315113781 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 253073102986866142630227563) ^ 1311259600968218355597034 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 253073102986866142630227563) ^ 15488897912165135114158 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 253073102986866142630227563) ^ 6306854 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_365031710759857615867563259 : Nat.Prime 365031710759857615867563259 := by
  apply lucas_primality 365031710759857615867563259 (2 : ZMod 365031710759857615867563259)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5530783496361479028296413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5530783496361479028296413, 1)] : List FactorBlock).map factorBlockValue).prod) = 365031710759857615867563259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_11
      · exact prime_oneHundredThirtyFourEB_5530783496361479028296413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 365031710759857615867563259) ^ 182515855379928807933781629 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 365031710759857615867563259) ^ 121677236919952538622521086 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 365031710759857615867563259) ^ 33184700978168874169778478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 365031710759857615867563259) ^ 66 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_367572534732664049388683189 : Nat.Prime 367572534732664049388683189 := by
  apply lucas_primality 367572534732664049388683189 (2 : ZMod 367572534732664049388683189)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 2), (4019, 1), (8017, 1), (19162813, 1), (58896389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 2), (4019, 1), (8017, 1), (19162813, 1), (58896389, 1)] : List FactorBlock).map factorBlockValue).prod) = 367572534732664049388683189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_7
      · exact prime_oneHundredThirtyFourEB_19
      · exact prime_oneHundredThirtyFourEB_4019
      · exact prime_oneHundredThirtyFourEB_8017
      · exact prime_oneHundredThirtyFourEB_19162813
      · exact prime_oneHundredThirtyFourEB_58896389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 367572534732664049388683189) ^ 183786267366332024694341594 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 367572534732664049388683189) ^ 52510362104666292769811884 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 367572534732664049388683189) ^ 19345922880666528915193852 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 367572534732664049388683189) ^ 91458704835198817961852 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 367572534732664049388683189) ^ 45849137424555825045364 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 367572534732664049388683189) ^ 19181554124264743876 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 367572534732664049388683189) ^ 6241002903126438692 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_443764040531591611446841609 : Nat.Prime 443764040531591611446841609 := by
  apply lucas_primality 443764040531591611446841609 (7 : ZMod 443764040531591611446841609)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (293, 1), (362429, 1), (174120659880621211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (293, 1), (362429, 1), (174120659880621211, 1)] : List FactorBlock).map factorBlockValue).prod) = 443764040531591611446841609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_293
      · exact prime_oneHundredThirtyFourEB_362429
      · exact prime_oneHundredThirtyFourEB_174120659880621211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 443764040531591611446841609) ^ 221882020265795805723420804 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 443764040531591611446841609) ^ 147921346843863870482280536 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 443764040531591611446841609) ^ 1514553039356967957156456 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 443764040531591611446841609) ^ 1224416480280528355752 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 443764040531591611446841609) ^ 2548600728 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_1147998278766508733960307641 : Nat.Prime 1147998278766508733960307641 := by
  apply lucas_primality 1147998278766508733960307641 (3 : ZMod 1147998278766508733960307641)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (12010951, 1), (2389482478878043741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (12010951, 1), (2389482478878043741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1147998278766508733960307641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_12010951
      · exact prime_oneHundredThirtyFourEB_2389482478878043741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1147998278766508733960307641) ^ 573999139383254366980153820 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1147998278766508733960307641) ^ 229599655753301746792061528 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1147998278766508733960307641) ^ 95579299155121749640 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1147998278766508733960307641) ^ 480438040 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_3684273545808795471779591963 : Nat.Prime 3684273545808795471779591963 := by
  apply lucas_primality 3684273545808795471779591963 (2 : ZMod 3684273545808795471779591963)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (73939, 1), (1083229461715149289273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (73939, 1), (1083229461715149289273, 1)] : List FactorBlock).map factorBlockValue).prod) = 3684273545808795471779591963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_23
      · exact prime_oneHundredThirtyFourEB_73939
      · exact prime_oneHundredThirtyFourEB_1083229461715149289273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3684273545808795471779591963) ^ 1842136772904397735889795981 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3684273545808795471779591963) ^ 160185806339512846599112694 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3684273545808795471779591963) ^ 49828555238896867306558 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3684273545808795471779591963) ^ 3401194 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_14402160224525291389683859499 : Nat.Prime 14402160224525291389683859499 := by
  apply lucas_primality 14402160224525291389683859499 (2 : ZMod 14402160224525291389683859499)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (631, 1), (1091, 1), (10460285366458381854769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (631, 1), (1091, 1), (10460285366458381854769, 1)] : List FactorBlock).map factorBlockValue).prod) = 14402160224525291389683859499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_631
      · exact prime_oneHundredThirtyFourEB_1091
      · exact prime_oneHundredThirtyFourEB_10460285366458381854769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14402160224525291389683859499) ^ 7201080112262645694841929749 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14402160224525291389683859499) ^ 22824342669612189207105958 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14402160224525291389683859499) ^ 13200880132470477900718478 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14402160224525291389683859499) ^ 1376842 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_26403960411629700881087075737 : Nat.Prime 26403960411629700881087075737 := by
  apply lucas_primality 26403960411629700881087075737 (7 : ZMod 26403960411629700881087075737)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (271, 1), (312280731521781872470043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (271, 1), (312280731521781872470043, 1)] : List FactorBlock).map factorBlockValue).prod) = 26403960411629700881087075737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_13
      · exact prime_oneHundredThirtyFourEB_271
      · exact prime_oneHundredThirtyFourEB_312280731521781872470043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26403960411629700881087075737) ^ 13201980205814850440543537868 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 26403960411629700881087075737) ^ 8801320137209900293695691912 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 26403960411629700881087075737) ^ 2031073877817669298545159672 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 26403960411629700881087075737) ^ 97431588234795944210653416 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 26403960411629700881087075737) ^ 84552 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_52807920823259401762174151491 : Nat.Prime 52807920823259401762174151491 := by
  apply lucas_primality 52807920823259401762174151491 (3 : ZMod 52807920823259401762174151491)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (41, 1), (349, 1), (4241998711787324733503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (41, 1), (349, 1), (4241998711787324733503, 1)] : List FactorBlock).map factorBlockValue).prod) = 52807920823259401762174151491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_5
      · exact prime_oneHundredThirtyFourEB_29
      · exact prime_oneHundredThirtyFourEB_41
      · exact prime_oneHundredThirtyFourEB_349
      · exact prime_oneHundredThirtyFourEB_4241998711787324733503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52807920823259401762174151491) ^ 26403960411629700881087075745 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52807920823259401762174151491) ^ 17602640274419800587391383830 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52807920823259401762174151491) ^ 10561584164651880352434830298 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52807920823259401762174151491) ^ 1820962787008944888350832810 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52807920823259401762174151491) ^ 1287998068859985408833515890 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52807920823259401762174151491) ^ 151312094049453873244052010 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52807920823259401762174151491) ^ 12448830 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_52807920823259401762174151497 : Nat.Prime 52807920823259401762174151497 := by
  apply lucas_primality 52807920823259401762174151497 (7 : ZMod 52807920823259401762174151497)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1483, 1), (572909, 1), (15059311, 1), (171971281987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1483, 1), (572909, 1), (15059311, 1), (171971281987, 1)] : List FactorBlock).map factorBlockValue).prod) = 52807920823259401762174151497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_1483
      · exact prime_oneHundredThirtyFourEB_572909
      · exact prime_oneHundredThirtyFourEB_15059311
      · exact prime_oneHundredThirtyFourEB_171971281987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 52807920823259401762174151497) ^ 26403960411629700881087075748 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52807920823259401762174151497) ^ 17602640274419800587391383832 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52807920823259401762174151497) ^ 35608847487025894647453912 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52807920823259401762174151497) ^ 92175058906841054621544 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52807920823259401762174151497) ^ 3506662477669755393336 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52807920823259401762174151497) ^ 307074066164438808 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFourEB_79211881234889102643261227227 : Nat.Prime 79211881234889102643261227227 := by
  apply lucas_primality 79211881234889102643261227227 (2 : ZMod 79211881234889102643261227227)
  · rw [← oneHundredThirtyFourEBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (43, 1), (38559717887, 1), (32766533662817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (43, 1), (38559717887, 1), (32766533662817, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889102643261227227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFourEB_2
      · exact prime_oneHundredThirtyFourEB_3
      · exact prime_oneHundredThirtyFourEB_43
      · exact prime_oneHundredThirtyFourEB_38559717887
      · exact prime_oneHundredThirtyFourEB_32766533662817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79211881234889102643261227227) ^ 39605940617444551321630613613 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889102643261227227) ^ 26403960411629700881087075742 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889102643261227227) ^ 1842136772904397735889795982 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889102643261227227) ^ 2054265061456648998 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889102643261227227) ^ 2417462953207578 ≠ 1
      rw [← oneHundredThirtyFourEBFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454400 : Nat.totient 158423762469778205286522454400 = 62423327186090473929689088000 := by
  rw [← show ((([(2, 7), (5, 2), (67, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_67, prime_oneHundredThirtyFourEB_171401, prime_oneHundredThirtyFourEB_714027719, prime_oneHundredThirtyFourEB_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454401 : Nat.totient 158423762469778205286522454401 = 95763711153501502364825655120 := by
  rw [← show ((([(3, 1), (11, 1), (383, 1), (12534517166688678320003359, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_383, prime_oneHundredThirtyFourEB_12534517166688678320003359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454402 : Nat.totient 158423762469778205286522454402 = 77217575571364382227953072000 := by
  rw [← show ((([(2, 1), (47, 1), (251, 1), (1079033, 1), (17872879, 1), (348168523819, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_47, prime_oneHundredThirtyFourEB_251, prime_oneHundredThirtyFourEB_1079033, prime_oneHundredThirtyFourEB_17872879, prime_oneHundredThirtyFourEB_348168523819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454403 : Nat.totient 158423762469778205286522454403 = 145957706736642031285136286720 := by
  rw [← show ((([(13, 1), (523, 1), (120193771681, 1), (193862281093037, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_523, prime_oneHundredThirtyFourEB_120193771681, prime_oneHundredThirtyFourEB_193862281093037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454404 : Nat.totient 158423762469778205286522454404 = 52807920823255729926063687264 := by
  rw [← show ((([(2, 2), (3, 1), (14614558068223, 1), (903344469547829, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_14614558068223, prime_oneHundredThirtyFourEB_903344469547829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454405 : Nat.totient 158423762469778205286522454405 = 125855740473039843716216448000 := by
  rw [← show ((([(5, 1), (163, 2), (1753, 1), (3821, 1), (135623, 1), (1312752365651, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_163, prime_oneHundredThirtyFourEB_1753, prime_oneHundredThirtyFourEB_3821, prime_oneHundredThirtyFourEB_135623, prime_oneHundredThirtyFourEB_1312752365651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454406 : Nat.totient 158423762469778205286522454406 = 65705707936774370856161386440 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1), (365031710759857615867563259, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_31, prime_oneHundredThirtyFourEB_365031710759857615867563259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454407 : Nat.totient 158423762469778205286522454407 = 105521738626111832944539928704 := by
  rw [← show ((([(3, 2), (1123, 1), (1915933, 1), (8181213754688881897, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_1123, prime_oneHundredThirtyFourEB_1915933, prime_oneHundredThirtyFourEB_8181213754688881897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454408 : Nat.totient 158423762469778205286522454408 = 75041051220068099525422270848 := by
  rw [← show ((([(2, 3), (19, 1), (42073, 1), (24772694963418564050723, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_19, prime_oneHundredThirtyFourEB_42073, prime_oneHundredThirtyFourEB_24772694963418564050723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454409 : Nat.totient 158423762469778205286522454409 = 154739488923969409814742862404 := by
  rw [← show ((([(43, 1), (3684273545808795471779591963, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_43, prime_oneHundredThirtyFourEB_3684273545808795471779591963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454410 : Nat.totient 158423762469778205286522454410 = 42244400263289255492270670720 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (21817, 1), (242049414783239683559491, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_21817, prime_oneHundredThirtyFourEB_242049414783239683559491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454411 : Nat.totient 158423762469778205286522454411 = 155434634756226023159507911872 := by
  rw [← show ((([(53, 1), (1297637543, 1), (2303515037688301609, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_53, prime_oneHundredThirtyFourEB_1297637543, prime_oneHundredThirtyFourEB_2303515037688301609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454412 : Nat.totient 158423762469778205286522454412 = 66504727865895240296827710720 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (29, 1), (8897178247, 1), (606721690722877, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_23, prime_oneHundredThirtyFourEB_29, prime_oneHundredThirtyFourEB_8897178247, prime_oneHundredThirtyFourEB_606721690722877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454413 : Nat.totient 158423762469778205286522454413 = 85202695782065589397793588736 := by
  rw [← show ((([(3, 1), (7, 1), (17, 1), (443764040531591611446841609, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_17, prime_oneHundredThirtyFourEB_443764040531591611446841609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454414 : Nat.totient 158423762469778205286522454414 = 77679408135382756616722636800 := by
  rw [← show ((([(2, 1), (109, 1), (113, 1), (701, 1), (339679, 1), (27008388370124849, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_109, prime_oneHundredThirtyFourEB_113, prime_oneHundredThirtyFourEB_701, prime_oneHundredThirtyFourEB_339679, prime_oneHundredThirtyFourEB_27008388370124849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454415 : Nat.totient 158423762469778205286522454415 = 126739000319495706377627031360 := by
  rw [← show ((([(5, 1), (13124971, 1), (2414081714462884608073, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_13124971, prime_oneHundredThirtyFourEB_2414081714462884608073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454416 : Nat.totient 158423762469778205286522454416 = 48565899366267516806540931840 := by
  rw [← show ((([(2, 4), (3, 2), (13, 1), (271, 1), (312280731521781872470043, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_271, prime_oneHundredThirtyFourEB_312280731521781872470043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454417 : Nat.totient 158423762469778205286522454417 = 157348461715783010535249369600 := by
  rw [← show ((([(191, 1), (641, 1), (1293984060162689231375407, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_191, prime_oneHundredThirtyFourEB_641, prime_oneHundredThirtyFourEB_1293984060162689231375407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454418 : Nat.totient 158423762469778205286522454418 = 79211881234839839871177802116 := by
  rw [← show ((([(2, 1), (1607998566547, 1), (49261164084858547, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_1607998566547, prime_oneHundredThirtyFourEB_49261164084858547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454419 : Nat.totient 158423762469778205286522454419 = 104728080569897941547038284672 := by
  rw [← show ((([(3, 1), (127, 1), (2239, 1), (11213, 1), (16562253663376706357, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_127, prime_oneHundredThirtyFourEB_2239, prime_oneHundredThirtyFourEB_11213, prime_oneHundredThirtyFourEB_16562253663376706357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454420 : Nat.totient 158423762469778205286522454420 = 52845480735489104063433984000 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (37, 1), (16421, 1), (1190451389, 1), (1564513433051, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_37, prime_oneHundredThirtyFourEB_16421, prime_oneHundredThirtyFourEB_1190451389, prime_oneHundredThirtyFourEB_1564513433051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454421 : Nat.totient 158423762469778205286522454421 = 158423762374845986265326664000 := by
  rw [← show ((([(1668809221, 1), (94932219019526981201, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_1668809221, prime_oneHundredThirtyFourEB_94932219019526981201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454422 : Nat.totient 158423762469778205286522454422 = 52807920823259401762174151472 := by
  rw [← show ((([(2, 1), (3, 1), (26403960411629700881087075737, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_26403960411629700881087075737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454423 : Nat.totient 158423762469778205286522454423 = 142048703584359038364005188800 := by
  rw [← show ((([(11, 1), (73, 1), (197289866089387553283340541, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_73, prime_oneHundredThirtyFourEB_197289866089387553283340541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454424 : Nat.totient 158423762469778205286522454424 = 79211881188630071035668953152 := by
  rw [← show ((([(2, 3), (1712354939, 1), (11564757900185713577, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_1712354939, prime_oneHundredThirtyFourEB_11564757900185713577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454425 : Nat.totient 158423762469778205286522454425 = 84487239073111934642659200000 := by
  rw [← show ((([(3, 3), (5, 2), (15551, 1), (86116861, 1), (175254846950641, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_15551, prime_oneHundredThirtyFourEB_86116861, prime_oneHundredThirtyFourEB_175254846950641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454426 : Nat.totient 158423762469778205286522454426 = 79115399040936740764280396640 := by
  rw [← show ((([(2, 1), (821, 1), (96482193952361878980829753, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_821, prime_oneHundredThirtyFourEB_96482193952361878980829753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454427 : Nat.totient 158423762469778205286522454427 = 127474266515419531278562867200 := by
  rw [← show ((([(7, 1), (19, 1), (131, 1), (677, 1), (33274412377, 1), (403643834681, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_19, prime_oneHundredThirtyFourEB_131, prime_oneHundredThirtyFourEB_677, prime_oneHundredThirtyFourEB_33274412377, prime_oneHundredThirtyFourEB_403643834681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454428 : Nat.totient 158423762469778205286522454428 = 52807920593099686364145877120 := by
  rw [← show ((([(2, 2), (3, 1), (229440329, 1), (57539928849277628261, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_229440329, prime_oneHundredThirtyFourEB_57539928849277628261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454429 : Nat.totient 158423762469778205286522454429 = 142670467848327623710427376000 := by
  rw [← show ((([(13, 3), (41, 1), (1631051, 1), (1078298171634392227, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_41, prime_oneHundredThirtyFourEB_1631051, prime_oneHundredThirtyFourEB_1078298171634392227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454430 : Nat.totient 158423762469778205286522454430 = 59641823676360608227335909376 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (941153, 1), (990173207880485302643, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_17, prime_oneHundredThirtyFourEB_941153, prime_oneHundredThirtyFourEB_990173207880485302643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454431 : Nat.totient 158423762469778205286522454431 = 102363391174452177953662545920 := by
  rw [← show ((([(3, 1), (59, 1), (71, 1), (6519017, 1), (75740297, 1), (25531691657, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_59, prime_oneHundredThirtyFourEB_71, prime_oneHundredThirtyFourEB_6519017, prime_oneHundredThirtyFourEB_75740297, prime_oneHundredThirtyFourEB_25531691657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454432 : Nat.totient 158423762469778205286522454432 = 79205692996997279048784363520 := by
  rw [← show ((([(2, 5), (12809, 1), (19049669, 1), (20289329043582881, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_12809, prime_oneHundredThirtyFourEB_19049669, prime_oneHundredThirtyFourEB_20289329043582881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454433 : Nat.totient 158423762469778205286522454433 = 158423762222354431695725814420 := by
  rw [← show ((([(640293211, 1), (247423773590156346803, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_640293211, prime_oneHundredThirtyFourEB_247423773590156346803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454434 : Nat.totient 158423762469778205286522454434 = 40394355165383959416268800000 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (11, 1), (97, 1), (157, 1), (571, 1), (206191, 1), (63749956565101, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_97, prime_oneHundredThirtyFourEB_157, prime_oneHundredThirtyFourEB_571, prime_oneHundredThirtyFourEB_206191, prime_oneHundredThirtyFourEB_63749956565101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454435 : Nat.totient 158423762469778205286522454435 = 119566336953395086323591230208 := by
  rw [← show ((([(5, 1), (23, 1), (79, 1), (937, 1), (18610403989568248797703, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_23, prime_oneHundredThirtyFourEB_79, prime_oneHundredThirtyFourEB_937, prime_oneHundredThirtyFourEB_18610403989568248797703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454436 : Nat.totient 158423762469778205286522454436 = 78871916079374557138354526208 := by
  rw [← show ((([(2, 2), (233, 1), (169982577757272752453350273, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_233, prime_oneHundredThirtyFourEB_169982577757272752453350273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454437 : Nat.totient 158423762469778205286522454437 = 102195868794602528024453324160 := by
  rw [← show ((([(3, 1), (31, 1), (7907, 1), (1218953, 1), (176741556522303979, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_31, prime_oneHundredThirtyFourEB_7907, prime_oneHundredThirtyFourEB_1218953, prime_oneHundredThirtyFourEB_176741556522303979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454438 : Nat.totient 158423762469778205286522454438 = 78958808131902236500630999344 := by
  rw [← show ((([(2, 1), (313, 1), (253073102986866142630227563, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_313, prime_oneHundredThirtyFourEB_253073102986866142630227563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454439 : Nat.totient 158423762469778205286522454439 = 155147424229662206026806161920 := by
  rw [← show ((([(89, 1), (107, 1), (4799, 1), (1411103081, 1), (2456614715147, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_89, prime_oneHundredThirtyFourEB_107, prime_oneHundredThirtyFourEB_4799, prime_oneHundredThirtyFourEB_1411103081, prime_oneHundredThirtyFourEB_2456614715147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454440 : Nat.totient 158423762469778205286522454440 = 42246004640337792253870318080 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (127241, 1), (10375570929036120779107, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_127241, prime_oneHundredThirtyFourEB_10375570929036120779107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454441 : Nat.totient 158423762469778205286522454441 = 131102588288143115907336057600 := by
  rw [← show ((([(7, 2), (29, 1), (19801, 1), (1180807, 1), (4768263011739203, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_29, prime_oneHundredThirtyFourEB_19801, prime_oneHundredThirtyFourEB_1180807, prime_oneHundredThirtyFourEB_4768263011739203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454442 : Nat.totient 158423762469778205286522454442 = 72592626059045034058989868608 := by
  rw [← show ((([(2, 1), (13, 1), (139, 1), (3615429029, 1), (12124737204839807, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_139, prime_oneHundredThirtyFourEB_3615429029, prime_oneHundredThirtyFourEB_12124737204839807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454443 : Nat.totient 158423762469778205286522454443 = 105142072479520659217295156352 := by
  rw [← show ((([(3, 2), (223, 1), (676037, 1), (116762258000298777577, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_223, prime_oneHundredThirtyFourEB_676037, prime_oneHundredThirtyFourEB_116762258000298777577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454444 : Nat.totient 158423762469778205286522454444 = 79211881122748746531511552448 := by
  rw [← show ((([(2, 2), (706363739, 1), (56070178055168473649, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_706363739, prime_oneHundredThirtyFourEB_56070178055168473649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454445 : Nat.totient 158423762469778205286522454445 = 115205701005992641467142056000 := by
  rw [← show ((([(5, 1), (11, 1), (9949, 1), (289519755242241258210551, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_9949, prime_oneHundredThirtyFourEB_289519755242241258210551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454446 : Nat.totient 158423762469778205286522454446 = 49994664465829218870514320000 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (2141, 1), (4751, 1), (136619840590887082229, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_19, prime_oneHundredThirtyFourEB_2141, prime_oneHundredThirtyFourEB_4751, prime_oneHundredThirtyFourEB_136619840590887082229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454447 : Nat.totient 158423762469778205286522454447 = 149104717618611182708424515712 := by
  rw [← show ((([(17, 1), (54768862156133, 1), (170152244985427, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_17, prime_oneHundredThirtyFourEB_54768862156133, prime_oneHundredThirtyFourEB_170152244985427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454448 : Nat.totient 158423762469778205286522454448 = 67776573248431348683965391360 := by
  rw [← show ((([(2, 4), (7, 1), (569, 1), (2485936518795163904194741, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_569, prime_oneHundredThirtyFourEB_2485936518795163904194741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454449 : Nat.totient 158423762469778205286522454449 = 102308846525740399814829559296 := by
  rw [← show ((([(3, 1), (47, 1), (103, 1), (1823, 1), (867253, 1), (6899720629650377, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_47, prime_oneHundredThirtyFourEB_103, prime_oneHundredThirtyFourEB_1823, prime_oneHundredThirtyFourEB_867253, prime_oneHundredThirtyFourEB_6899720629650377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454450 : Nat.totient 158423762469778205286522454450 = 62729983004162703892382720000 := by
  rw [← show ((([(2, 1), (5, 2), (101, 1), (5261, 1), (426077, 1), (2238809, 1), (6251086493, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_101, prime_oneHundredThirtyFourEB_5261, prime_oneHundredThirtyFourEB_426077, prime_oneHundredThirtyFourEB_2238809, prime_oneHundredThirtyFourEB_6251086493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454451 : Nat.totient 158423762469778205286522454451 = 157821339773080693073449800000 := by
  rw [← show ((([(263, 1), (3095977, 1), (194565954597662587501, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_263, prime_oneHundredThirtyFourEB_3095977, prime_oneHundredThirtyFourEB_194565954597662587501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454452 : Nat.totient 158423762469778205286522454452 = 51579829639983901472740468224 := by
  rw [← show ((([(2, 2), (3, 6), (43, 1), (38559717887, 1), (32766533662817, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_43, prime_oneHundredThirtyFourEB_38559717887, prime_oneHundredThirtyFourEB_32766533662817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454453 : Nat.totient 158423762469778205286522454453 = 158423762469774851658417103020 := by
  rw [← show ((([(47924368019023, 1), (3305703737332411, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_47924368019023, prime_oneHundredThirtyFourEB_3305703737332411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454454 : Nat.totient 158423762469778205286522454454 = 79211881234889102643261227226 := by
  rw [← show ((([(2, 1), (79211881234889102643261227227, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_79211881234889102643261227227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454455 : Nat.totient 158423762469778205286522454455 = 66851345921266162896761410560 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (13, 1), (1453260517097, 1), (79862738360611, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_1453260517097, prime_oneHundredThirtyFourEB_79862738360611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454456 : Nat.totient 158423762469778205286522454456 = 71825673845917490646756994560 := by
  rw [← show ((([(2, 3), (11, 1), (389, 1), (7532029, 1), (614435169710353877, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_389, prime_oneHundredThirtyFourEB_7532029, prime_oneHundredThirtyFourEB_614435169710353877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454457 : Nat.totient 158423762469778205286522454457 = 150707785501551970015527168000 := by
  rw [← show ((([(37, 1), (61, 1), (179, 1), (2617, 1), (94847, 1), (134191, 1), (11772942491, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_37, prime_oneHundredThirtyFourEB_61, prime_oneHundredThirtyFourEB_179, prime_oneHundredThirtyFourEB_2617, prime_oneHundredThirtyFourEB_94847, prime_oneHundredThirtyFourEB_134191, prime_oneHundredThirtyFourEB_11772942491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454458 : Nat.totient 158423762469778205286522454458 = 50511924265726384294253536160 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (1147998278766508733960307641, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_23, prime_oneHundredThirtyFourEB_1147998278766508733960307641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454459 : Nat.totient 158423762469778205286522454459 = 158056189935045541237133770840 := by
  rw [← show ((([(431, 1), (367572534732664049388683189, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_431, prime_oneHundredThirtyFourEB_367572534732664049388683189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454460 : Nat.totient 158423762469778205286522454460 = 63369501167814809964819408384 := by
  rw [← show ((([(2, 2), (5, 1), (16866029, 1), (1010148583, 1), (464934984089, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_16866029, prime_oneHundredThirtyFourEB_1010148583, prime_oneHundredThirtyFourEB_464934984089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454461 : Nat.totient 158423762469778205286522454461 = 103733079610475743179568992000 := by
  rw [← show ((([(3, 2), (83, 1), (211, 1), (953, 1), (15271, 1), (69064820657869891, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_83, prime_oneHundredThirtyFourEB_211, prime_oneHundredThirtyFourEB_953, prime_oneHundredThirtyFourEB_15271, prime_oneHundredThirtyFourEB_69064820657869891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454462 : Nat.totient 158423762469778205286522454462 = 67895898190557267536997429600 := by
  rw [← show ((([(2, 1), (7, 1), (6300513133, 1), (1796041496094376301, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_6300513133, prime_oneHundredThirtyFourEB_1796041496094376301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454463 : Nat.totient 158423762469778205286522454463 = 158423383248752712895113712000 := by
  rw [← show ((([(420521, 1), (63651503, 1), (5918667894497801, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_420521, prime_oneHundredThirtyFourEB_63651503, prime_oneHundredThirtyFourEB_5918667894497801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454464 : Nat.totient 158423762469778205286522454464 = 48763523197543808686503444480 := by
  rw [← show ((([(2, 6), (3, 1), (17, 1), (53, 1), (171811, 1), (5330197951516363747, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_17, prime_oneHundredThirtyFourEB_53, prime_oneHundredThirtyFourEB_171811, prime_oneHundredThirtyFourEB_5330197951516363747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454465 : Nat.totient 158423762469778205286522454465 = 119848240355864620201795353600 := by
  rw [← show ((([(5, 1), (19, 1), (593, 1), (7019, 1), (161611, 1), (2479110385407431, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_19, prime_oneHundredThirtyFourEB_593, prime_oneHundredThirtyFourEB_7019, prime_oneHundredThirtyFourEB_161611, prime_oneHundredThirtyFourEB_2479110385407431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454466 : Nat.totient 158423762469778205286522454466 = 79211127058681745871425728260 := by
  rw [← show ((([(2, 1), (105031, 1), (754176207356771835393943, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_105031, prime_oneHundredThirtyFourEB_754176207356771835393943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454467 : Nat.totient 158423762469778205286522454467 = 94374836819425221615059328000 := by
  rw [← show ((([(3, 1), (11, 1), (67, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_67, prime_oneHundredThirtyFourEB_461, prime_oneHundredThirtyFourEB_69997, prime_oneHundredThirtyFourEB_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454468 : Nat.totient 158423762469778205286522454468 = 70759992328016273892873648000 := by
  rw [← show ((([(2, 2), (13, 1), (31, 1), (84776639, 1), (1159255302412969301, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_31, prime_oneHundredThirtyFourEB_84776639, prime_oneHundredThirtyFourEB_1159255302412969301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454469 : Nat.totient 158423762469778205286522454469 = 135791775864893259205931130480 := by
  rw [← show ((([(7, 1), (6611807, 1), (3422962295649460455181, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_6611807, prime_oneHundredThirtyFourEB_3422962295649460455181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454470 : Nat.totient 158423762469778205286522454470 = 39680674029749464515113748480 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (29, 1), (41, 1), (349, 1), (4241998711787324733503, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_29, prime_oneHundredThirtyFourEB_41, prime_oneHundredThirtyFourEB_349, prime_oneHundredThirtyFourEB_4241998711787324733503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454471 : Nat.totient 158423762469778205286522454471 = 158062887776977340778736898712 := by
  rw [← show ((([(439, 1), (304781783, 1), (1184041154424372983, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_439, prime_oneHundredThirtyFourEB_304781783, prime_oneHundredThirtyFourEB_1184041154424372983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454472 : Nat.totient 158423762469778205286522454472 = 79211843908173716735318729616 := by
  rw [← show ((([(2, 3), (2122123, 1), (9331678846476983502283, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_2122123, prime_oneHundredThirtyFourEB_9331678846476983502283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454473 : Nat.totient 158423762469778205286522454473 = 105615841646518803524348302980 := by
  rw [← show ((([(3, 1), (52807920823259401762174151491, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_52807920823259401762174151491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454474 : Nat.totient 158423762469778205286522454474 = 78754009084257357775968235200 := by
  rw [← show ((([(2, 1), (173, 1), (16526450869, 1), (27705412946543701, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_173, prime_oneHundredThirtyFourEB_16526450869, prime_oneHundredThirtyFourEB_27705412946543701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454475 : Nat.totient 158423762469778205286522454475 = 126354175582491777038129256960 := by
  rw [← show ((([(5, 2), (599, 1), (733, 1), (200003, 1), (53757983, 1), (1342363213, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_599, prime_oneHundredThirtyFourEB_733, prime_oneHundredThirtyFourEB_200003, prime_oneHundredThirtyFourEB_53757983, prime_oneHundredThirtyFourEB_1342363213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454476 : Nat.totient 158423762469778205286522454476 = 45263377774692056811716515584 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (83869, 1), (3087223, 1), (7284027409406597, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_83869, prime_oneHundredThirtyFourEB_3087223, prime_oneHundredThirtyFourEB_7284027409406597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454477 : Nat.totient 158423762469778205286522454477 = 158423738001363214980793888156 := by
  rw [← show ((([(6474623, 1), (24468414990305722091699, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_6474623, prime_oneHundredThirtyFourEB_24468414990305722091699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454478 : Nat.totient 158423762469778205286522454478 = 71830779611469708196691856000 := by
  rw [← show ((([(2, 1), (11, 1), (631, 1), (1091, 1), (10460285366458381854769, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_631, prime_oneHundredThirtyFourEB_1091, prime_oneHundredThirtyFourEB_10460285366458381854769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454479 : Nat.totient 158423762469778205286522454479 = 105615702601648478280807575040 := by
  rw [← show ((([(3, 3), (759581, 1), (7724715018069084836417, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_759581, prime_oneHundredThirtyFourEB_7724715018069084836417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454480 : Nat.totient 158423762469778205286522454480 = 63369065016620463393064464000 := by
  rw [← show ((([(2, 4), (5, 1), (144031, 1), (13749102838085048122151, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_144031, prime_oneHundredThirtyFourEB_13749102838085048122151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454481 : Nat.totient 158423762469778205286522454481 = 131535841166003686140756099072 := by
  rw [← show ((([(13, 1), (17, 1), (23, 1), (2417, 1), (2557, 1), (14639, 1), (579829, 1), (594130013, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_17, prime_oneHundredThirtyFourEB_23, prime_oneHundredThirtyFourEB_2417, prime_oneHundredThirtyFourEB_2557, prime_oneHundredThirtyFourEB_14639, prime_oneHundredThirtyFourEB_579829, prime_oneHundredThirtyFourEB_594130013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454482 : Nat.totient 158423762469778205286522454482 = 52389880775550630135080702208 := by
  rw [← show ((([(2, 1), (3, 1), (137, 1), (1609, 1), (119782248627155194009459, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_137, prime_oneHundredThirtyFourEB_1609, prime_oneHundredThirtyFourEB_119782248627155194009459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454483 : Nat.totient 158423762469778205286522454483 = 135130051179907591364439289344 := by
  rw [← show ((([(7, 1), (227, 1), (5399, 1), (6833, 1), (7219, 1), (374364480242939, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_227, prime_oneHundredThirtyFourEB_5399, prime_oneHundredThirtyFourEB_6833, prime_oneHundredThirtyFourEB_7219, prime_oneHundredThirtyFourEB_374364480242939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454484 : Nat.totient 158423762469778205286522454484 = 74833801887938040966599510400 := by
  rw [← show ((([(2, 2), (19, 1), (359, 1), (5806471282428463762150801, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_19, prime_oneHundredThirtyFourEB_359, prime_oneHundredThirtyFourEB_5806471282428463762150801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454485 : Nat.totient 158423762469778205286522454485 = 83933118856678694315683584000 := by
  rw [← show ((([(3, 1), (5, 1), (151, 1), (252348641, 1), (277173143132052989, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_151, prime_oneHundredThirtyFourEB_252348641, prime_oneHundredThirtyFourEB_277173143132052989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454486 : Nat.totient 158423762469778205286522454486 = 78999489548275984830743148000 := by
  rw [← show ((([(2, 1), (373, 1), (2883851, 1), (73639134911939129341, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_373, prime_oneHundredThirtyFourEB_2883851, prime_oneHundredThirtyFourEB_73639134911939129341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454487 : Nat.totient 158423762469778205286522454487 = 157819745300641440398245484064 := by
  rw [← show ((([(277, 1), (4919, 1), (116268944973390738840349, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_277, prime_oneHundredThirtyFourEB_4919, prime_oneHundredThirtyFourEB_116268944973390738840349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454488 : Nat.totient 158423762469778205286522454488 = 52772216358269271512739767040 := by
  rw [← show ((([(2, 3), (3, 2), (1483, 1), (572909, 1), (15059311, 1), (171971281987, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_1483, prime_oneHundredThirtyFourEB_572909, prime_oneHundredThirtyFourEB_15059311, prime_oneHundredThirtyFourEB_171971281987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454489 : Nat.totient 158423762469778205286522454489 = 144021602245252913896838594980 := by
  rw [← show ((([(11, 1), (14402160224525291389683859499, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_14402160224525291389683859499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454490 : Nat.totient 158423762469778205286522454490 = 53396095884161491426494291840 := by
  rw [← show ((([(2, 1), (5, 1), (7, 2), (59, 1), (162588421, 1), (33704090966624959, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_59, prime_oneHundredThirtyFourEB_162588421, prime_oneHundredThirtyFourEB_33704090966624959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454491 : Nat.totient 158423762469778205286522454491 = 105615841646518803524348302992 := by
  rw [← show ((([(3, 1), (52807920823259401762174151497, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_52807920823259401762174151497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454492 : Nat.totient 158423762469778205286522454492 = 78980454464068175918471040000 := by
  rw [← show ((([(2, 2), (491, 1), (1181, 1), (24977, 1), (49821451, 1), (54887354219, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_491, prime_oneHundredThirtyFourEB_1181, prime_oneHundredThirtyFourEB_24977, prime_oneHundredThirtyFourEB_49821451, prime_oneHundredThirtyFourEB_54887354219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454493 : Nat.totient 158423762469778205286522454493 = 158416428195591634320335308800 := by
  rw [← show ((([(21601, 1), (878723089, 1), (8346308408302637, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_21601, prime_oneHundredThirtyFourEB_878723089, prime_oneHundredThirtyFourEB_8346308408302637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454494 : Nat.totient 158423762469778205286522454494 = 47428319741472061457919403392 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (37, 1), (54893888589666737798517829, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_13, prime_oneHundredThirtyFourEB_37, prime_oneHundredThirtyFourEB_54893888589666737798517829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454495 : Nat.totient 158423762469778205286522454495 = 123544485336349607672224801152 := by
  rw [← show ((([(5, 1), (43, 1), (503, 1), (123637, 1), (11848555844366480563, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_43, prime_oneHundredThirtyFourEB_503, prime_oneHundredThirtyFourEB_123637, prime_oneHundredThirtyFourEB_11848555844366480563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454496 : Nat.totient 158423762469778205286522454496 = 76433835786643527445324431360 := by
  rw [← show ((([(2, 5), (47, 1), (73, 1), (2671, 1), (42043, 1), (327473, 1), (39237971077, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_47, prime_oneHundredThirtyFourEB_73, prime_oneHundredThirtyFourEB_2671, prime_oneHundredThirtyFourEB_42043, prime_oneHundredThirtyFourEB_327473, prime_oneHundredThirtyFourEB_39237971077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454497 : Nat.totient 158423762469778205286522454497 = 90271411395084831497092125696 := by
  rw [← show ((([(3, 2), (7, 1), (353, 1), (1539544962509, 1), (4627140549947, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_7, prime_oneHundredThirtyFourEB_353, prime_oneHundredThirtyFourEB_1539544962509, prime_oneHundredThirtyFourEB_4627140549947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454498 : Nat.totient 158423762469778205286522454498 = 74552358731761145622035419200 := by
  rw [← show ((([(2, 1), (17, 1), (961392247, 1), (4846640317853230951, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_17, prime_oneHundredThirtyFourEB_961392247, prime_oneHundredThirtyFourEB_4846640317853230951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454499 : Nat.totient 158423762469778205286522454499 = 148026652363307778020777376000 := by
  rw [← show ((([(29, 1), (31, 1), (176222205194414021453306401, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_29, prime_oneHundredThirtyFourEB_31, prime_oneHundredThirtyFourEB_176222205194414021453306401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454500 : Nat.totient 158423762469778205286522454500 = 38405760217415322361086592000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 3), (11, 1), (100718249, 1), (95329696902132677, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_2, prime_oneHundredThirtyFourEB_3, prime_oneHundredThirtyFourEB_5, prime_oneHundredThirtyFourEB_11, prime_oneHundredThirtyFourEB_100718249, prime_oneHundredThirtyFourEB_95329696902132677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFourEB_158423762469778205286522454501 : Nat.totient 158423762469778205286522454501 = 158423762469777376013731520812 := by
  rw [← show ((([(298448711197127, 1), (530824079736563, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778205286522454501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFourEB_298448711197127, prime_oneHundredThirtyFourEB_530824079736563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyFourEB : certifiedKill 1 158423762469778205286522454399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyFourEB_158423762469778205286522454400, phi_oneHundredThirtyFourEB_158423762469778205286522454401, phi_oneHundredThirtyFourEB_158423762469778205286522454402,
    phi_oneHundredThirtyFourEB_158423762469778205286522454403, phi_oneHundredThirtyFourEB_158423762469778205286522454404, phi_oneHundredThirtyFourEB_158423762469778205286522454405,
    phi_oneHundredThirtyFourEB_158423762469778205286522454406, phi_oneHundredThirtyFourEB_158423762469778205286522454407, phi_oneHundredThirtyFourEB_158423762469778205286522454408,
    phi_oneHundredThirtyFourEB_158423762469778205286522454409, phi_oneHundredThirtyFourEB_158423762469778205286522454410, phi_oneHundredThirtyFourEB_158423762469778205286522454411,
    phi_oneHundredThirtyFourEB_158423762469778205286522454412, phi_oneHundredThirtyFourEB_158423762469778205286522454413, phi_oneHundredThirtyFourEB_158423762469778205286522454414,
    phi_oneHundredThirtyFourEB_158423762469778205286522454415, phi_oneHundredThirtyFourEB_158423762469778205286522454416, phi_oneHundredThirtyFourEB_158423762469778205286522454417,
    phi_oneHundredThirtyFourEB_158423762469778205286522454418, phi_oneHundredThirtyFourEB_158423762469778205286522454419, phi_oneHundredThirtyFourEB_158423762469778205286522454420,
    phi_oneHundredThirtyFourEB_158423762469778205286522454421, phi_oneHundredThirtyFourEB_158423762469778205286522454422, phi_oneHundredThirtyFourEB_158423762469778205286522454423,
    phi_oneHundredThirtyFourEB_158423762469778205286522454424, phi_oneHundredThirtyFourEB_158423762469778205286522454425, phi_oneHundredThirtyFourEB_158423762469778205286522454426,
    phi_oneHundredThirtyFourEB_158423762469778205286522454427, phi_oneHundredThirtyFourEB_158423762469778205286522454428, phi_oneHundredThirtyFourEB_158423762469778205286522454429,
    phi_oneHundredThirtyFourEB_158423762469778205286522454430, phi_oneHundredThirtyFourEB_158423762469778205286522454431, phi_oneHundredThirtyFourEB_158423762469778205286522454432,
    phi_oneHundredThirtyFourEB_158423762469778205286522454433, phi_oneHundredThirtyFourEB_158423762469778205286522454434, phi_oneHundredThirtyFourEB_158423762469778205286522454435,
    phi_oneHundredThirtyFourEB_158423762469778205286522454436, phi_oneHundredThirtyFourEB_158423762469778205286522454437, phi_oneHundredThirtyFourEB_158423762469778205286522454438,
    phi_oneHundredThirtyFourEB_158423762469778205286522454439, phi_oneHundredThirtyFourEB_158423762469778205286522454440, phi_oneHundredThirtyFourEB_158423762469778205286522454441,
    phi_oneHundredThirtyFourEB_158423762469778205286522454442, phi_oneHundredThirtyFourEB_158423762469778205286522454443, phi_oneHundredThirtyFourEB_158423762469778205286522454444,
    phi_oneHundredThirtyFourEB_158423762469778205286522454445, phi_oneHundredThirtyFourEB_158423762469778205286522454446, phi_oneHundredThirtyFourEB_158423762469778205286522454447,
    phi_oneHundredThirtyFourEB_158423762469778205286522454448, phi_oneHundredThirtyFourEB_158423762469778205286522454449, phi_oneHundredThirtyFourEB_158423762469778205286522454450,
    phi_oneHundredThirtyFourEB_158423762469778205286522454451, phi_oneHundredThirtyFourEB_158423762469778205286522454452, phi_oneHundredThirtyFourEB_158423762469778205286522454453,
    phi_oneHundredThirtyFourEB_158423762469778205286522454454, phi_oneHundredThirtyFourEB_158423762469778205286522454455, phi_oneHundredThirtyFourEB_158423762469778205286522454456,
    phi_oneHundredThirtyFourEB_158423762469778205286522454457, phi_oneHundredThirtyFourEB_158423762469778205286522454458, phi_oneHundredThirtyFourEB_158423762469778205286522454459,
    phi_oneHundredThirtyFourEB_158423762469778205286522454460, phi_oneHundredThirtyFourEB_158423762469778205286522454461, phi_oneHundredThirtyFourEB_158423762469778205286522454462,
    phi_oneHundredThirtyFourEB_158423762469778205286522454463, phi_oneHundredThirtyFourEB_158423762469778205286522454464, phi_oneHundredThirtyFourEB_158423762469778205286522454465,
    phi_oneHundredThirtyFourEB_158423762469778205286522454466, phi_oneHundredThirtyFourEB_158423762469778205286522454467, phi_oneHundredThirtyFourEB_158423762469778205286522454468,
    phi_oneHundredThirtyFourEB_158423762469778205286522454469, phi_oneHundredThirtyFourEB_158423762469778205286522454470, phi_oneHundredThirtyFourEB_158423762469778205286522454471,
    phi_oneHundredThirtyFourEB_158423762469778205286522454472, phi_oneHundredThirtyFourEB_158423762469778205286522454473, phi_oneHundredThirtyFourEB_158423762469778205286522454474,
    phi_oneHundredThirtyFourEB_158423762469778205286522454475, phi_oneHundredThirtyFourEB_158423762469778205286522454476, phi_oneHundredThirtyFourEB_158423762469778205286522454477,
    phi_oneHundredThirtyFourEB_158423762469778205286522454478, phi_oneHundredThirtyFourEB_158423762469778205286522454479, phi_oneHundredThirtyFourEB_158423762469778205286522454480,
    phi_oneHundredThirtyFourEB_158423762469778205286522454481, phi_oneHundredThirtyFourEB_158423762469778205286522454482, phi_oneHundredThirtyFourEB_158423762469778205286522454483,
    phi_oneHundredThirtyFourEB_158423762469778205286522454484, phi_oneHundredThirtyFourEB_158423762469778205286522454485, phi_oneHundredThirtyFourEB_158423762469778205286522454486,
    phi_oneHundredThirtyFourEB_158423762469778205286522454487, phi_oneHundredThirtyFourEB_158423762469778205286522454488, phi_oneHundredThirtyFourEB_158423762469778205286522454489,
    phi_oneHundredThirtyFourEB_158423762469778205286522454490, phi_oneHundredThirtyFourEB_158423762469778205286522454491, phi_oneHundredThirtyFourEB_158423762469778205286522454492,
    phi_oneHundredThirtyFourEB_158423762469778205286522454493, phi_oneHundredThirtyFourEB_158423762469778205286522454494, phi_oneHundredThirtyFourEB_158423762469778205286522454495,
    phi_oneHundredThirtyFourEB_158423762469778205286522454496, phi_oneHundredThirtyFourEB_158423762469778205286522454497, phi_oneHundredThirtyFourEB_158423762469778205286522454498,
    phi_oneHundredThirtyFourEB_158423762469778205286522454499, phi_oneHundredThirtyFourEB_158423762469778205286522454500, phi_oneHundredThirtyFourEB_158423762469778205286522454501]

end TotientTailPeriodKiller
end Erdos249257
