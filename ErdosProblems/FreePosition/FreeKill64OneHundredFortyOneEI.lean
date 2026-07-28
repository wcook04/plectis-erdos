import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFortyOneEIFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyOneEIFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyOneEIFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyOneEIFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyOneEIFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyOneEIFastPow a n * oneHundredFortyOneEIFastPow a n * a else oneHundredFortyOneEIFastPow a n * oneHundredFortyOneEIFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyOneEI_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_331 : Nat.Prime 331 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_397 : Nat.Prime 397 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_443 : Nat.Prime 443 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_467 : Nat.Prime 467 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_499 : Nat.Prime 499 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_509 : Nat.Prime 509 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_521 : Nat.Prime 521 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_563 : Nat.Prime 563 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_569 : Nat.Prime 569 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_571 : Nat.Prime 571 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_587 : Nat.Prime 587 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_599 : Nat.Prime 599 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_607 : Nat.Prime 607 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_619 : Nat.Prime 619 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_647 : Nat.Prime 647 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_677 : Nat.Prime 677 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_761 : Nat.Prime 761 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_809 : Nat.Prime 809 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_811 : Nat.Prime 811 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_829 : Nat.Prime 829 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_863 : Nat.Prime 863 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_877 : Nat.Prime 877 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_881 : Nat.Prime 881 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_883 : Nat.Prime 883 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_911 : Nat.Prime 911 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_971 : Nat.Prime 971 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_977 : Nat.Prime 977 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_983 : Nat.Prime 983 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1013 : Nat.Prime 1013 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1021 : Nat.Prime 1021 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1039 : Nat.Prime 1039 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1049 : Nat.Prime 1049 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1103 : Nat.Prime 1103 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1123 : Nat.Prime 1123 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1151 : Nat.Prime 1151 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1217 : Nat.Prime 1217 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1223 : Nat.Prime 1223 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1249 : Nat.Prime 1249 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1291 : Nat.Prime 1291 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1297 : Nat.Prime 1297 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1367 : Nat.Prime 1367 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1409 : Nat.Prime 1409 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1427 : Nat.Prime 1427 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1447 : Nat.Prime 1447 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1453 : Nat.Prime 1453 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1481 : Nat.Prime 1481 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1487 : Nat.Prime 1487 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1489 : Nat.Prime 1489 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1627 : Nat.Prime 1627 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1693 : Nat.Prime 1693 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1699 : Nat.Prime 1699 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1783 : Nat.Prime 1783 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1787 : Nat.Prime 1787 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1823 : Nat.Prime 1823 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1871 : Nat.Prime 1871 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1879 : Nat.Prime 1879 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1951 : Nat.Prime 1951 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1973 : Nat.Prime 1973 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1979 : Nat.Prime 1979 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1987 : Nat.Prime 1987 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2017 : Nat.Prime 2017 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2027 : Nat.Prime 2027 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2029 : Nat.Prime 2029 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2129 : Nat.Prime 2129 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2141 : Nat.Prime 2141 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2347 : Nat.Prime 2347 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2351 : Nat.Prime 2351 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2357 : Nat.Prime 2357 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2389 : Nat.Prime 2389 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2447 : Nat.Prime 2447 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2477 : Nat.Prime 2477 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2521 : Nat.Prime 2521 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2551 : Nat.Prime 2551 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2557 : Nat.Prime 2557 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2609 : Nat.Prime 2609 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2621 : Nat.Prime 2621 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2671 : Nat.Prime 2671 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2683 : Nat.Prime 2683 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2897 : Nat.Prime 2897 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2939 : Nat.Prime 2939 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3041 : Nat.Prime 3041 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3049 : Nat.Prime 3049 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3089 : Nat.Prime 3089 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3361 : Nat.Prime 3361 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3373 : Nat.Prime 3373 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3461 : Nat.Prime 3461 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3463 : Nat.Prime 3463 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3517 : Nat.Prime 3517 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3617 : Nat.Prime 3617 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3847 : Nat.Prime 3847 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3881 : Nat.Prime 3881 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3907 : Nat.Prime 3907 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4003 : Nat.Prime 4003 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4139 : Nat.Prime 4139 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4397 : Nat.Prime 4397 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4517 : Nat.Prime 4517 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4549 : Nat.Prime 4549 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4567 : Nat.Prime 4567 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4639 : Nat.Prime 4639 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4973 : Nat.Prime 4973 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5563 : Nat.Prime 5563 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5569 : Nat.Prime 5569 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5657 : Nat.Prime 5657 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5701 : Nat.Prime 5701 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5987 : Nat.Prime 5987 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6043 : Nat.Prime 6043 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6229 : Nat.Prime 6229 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6397 : Nat.Prime 6397 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6491 : Nat.Prime 6491 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7027 : Nat.Prime 7027 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7121 : Nat.Prime 7121 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7901 : Nat.Prime 7901 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7993 : Nat.Prime 7993 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_8081 : Nat.Prime 8081 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_8641 : Nat.Prime 8641 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_8887 : Nat.Prime 8887 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9133 : Nat.Prime 9133 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9203 : Nat.Prime 9203 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9311 : Nat.Prime 9311 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9619 : Nat.Prime 9619 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9767 : Nat.Prime 9767 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_10357 : Nat.Prime 10357 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_10837 : Nat.Prime 10837 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_11149 : Nat.Prime 11149 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_11519 : Nat.Prime 11519 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_11903 : Nat.Prime 11903 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_12379 : Nat.Prime 12379 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_12553 : Nat.Prime 12553 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_12893 : Nat.Prime 12893 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_12979 : Nat.Prime 12979 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_13313 : Nat.Prime 13313 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_13381 : Nat.Prime 13381 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_13967 : Nat.Prime 13967 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_14009 : Nat.Prime 14009 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_14011 : Nat.Prime 14011 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_14449 : Nat.Prime 14449 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_14747 : Nat.Prime 14747 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_15991 : Nat.Prime 15991 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_17047 : Nat.Prime 17047 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_18199 : Nat.Prime 18199 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_18313 : Nat.Prime 18313 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_18713 : Nat.Prime 18713 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_20599 : Nat.Prime 20599 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_22273 : Nat.Prime 22273 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_22817 : Nat.Prime 22817 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_23431 : Nat.Prime 23431 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_23977 : Nat.Prime 23977 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_23981 : Nat.Prime 23981 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_24083 : Nat.Prime 24083 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_25343 : Nat.Prime 25343 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_26053 : Nat.Prime 26053 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_27361 : Nat.Prime 27361 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_27893 : Nat.Prime 27893 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_28181 : Nat.Prime 28181 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_30493 : Nat.Prime 30493 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_30517 : Nat.Prime 30517 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_34469 : Nat.Prime 34469 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_34897 : Nat.Prime 34897 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_38299 : Nat.Prime 38299 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_39367 : Nat.Prime 39367 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_39419 : Nat.Prime 39419 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_42209 : Nat.Prime 42209 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_43651 : Nat.Prime 43651 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_44293 : Nat.Prime 44293 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_45893 : Nat.Prime 45893 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_47129 : Nat.Prime 47129 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_47713 : Nat.Prime 47713 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_50101 : Nat.Prime 50101 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_51539 : Nat.Prime 51539 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_51719 : Nat.Prime 51719 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_52021 : Nat.Prime 52021 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_53887 : Nat.Prime 53887 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_58481 : Nat.Prime 58481 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_62141 : Nat.Prime 62141 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_65927 : Nat.Prime 65927 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_68489 : Nat.Prime 68489 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_70949 : Nat.Prime 70949 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_71359 : Nat.Prime 71359 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_72307 : Nat.Prime 72307 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_82003 : Nat.Prime 82003 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_82241 : Nat.Prime 82241 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_84653 : Nat.Prime 84653 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_89123 : Nat.Prime 89123 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_90203 : Nat.Prime 90203 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_90989 : Nat.Prime 90989 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_91129 : Nat.Prime 91129 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_92173 : Nat.Prime 92173 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_99149 : Nat.Prime 99149 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_111641 : Nat.Prime 111641 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_113963 : Nat.Prime 113963 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_128969 : Nat.Prime 128969 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_152381 : Nat.Prime 152381 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_153487 : Nat.Prime 153487 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_154571 : Nat.Prime 154571 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_156971 : Nat.Prime 156971 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_157259 : Nat.Prime 157259 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_159113 : Nat.Prime 159113 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_162937 : Nat.Prime 162937 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_168743 : Nat.Prime 168743 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_171491 : Nat.Prime 171491 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_173191 : Nat.Prime 173191 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_173779 : Nat.Prime 173779 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_174721 : Nat.Prime 174721 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_184843 : Nat.Prime 184843 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_190301 : Nat.Prime 190301 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_214189 : Nat.Prime 214189 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_215261 : Nat.Prime 215261 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_230213 : Nat.Prime 230213 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_241973 : Nat.Prime 241973 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_243953 : Nat.Prime 243953 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_246613 : Nat.Prime 246613 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_248407 : Nat.Prime 248407 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_257189 : Nat.Prime 257189 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_265541 : Nat.Prime 265541 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_284117 : Nat.Prime 284117 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_290359 : Nat.Prime 290359 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_306703 : Nat.Prime 306703 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_311393 : Nat.Prime 311393 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_331693 : Nat.Prime 331693 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_336761 : Nat.Prime 336761 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_341461 : Nat.Prime 341461 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_355867 : Nat.Prime 355867 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_357283 : Nat.Prime 357283 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_369253 : Nat.Prime 369253 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_372313 : Nat.Prime 372313 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_374929 : Nat.Prime 374929 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_380867 : Nat.Prime 380867 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_388727 : Nat.Prime 388727 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_400711 : Nat.Prime 400711 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_402137 : Nat.Prime 402137 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_402767 : Nat.Prime 402767 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_414019 : Nat.Prime 414019 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_418553 : Nat.Prime 418553 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_447541 : Nat.Prime 447541 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_449417 : Nat.Prime 449417 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_449959 : Nat.Prime 449959 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_470621 : Nat.Prime 470621 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_519119 : Nat.Prime 519119 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_519787 : Nat.Prime 519787 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_520549 : Nat.Prime 520549 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_529127 : Nat.Prime 529127 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_531133 : Nat.Prime 531133 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_534091 : Nat.Prime 534091 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_566023 : Nat.Prime 566023 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_580763 : Nat.Prime 580763 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_589609 : Nat.Prime 589609 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_669947 : Nat.Prime 669947 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_677813 : Nat.Prime 677813 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_713917 : Nat.Prime 713917 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_737857 : Nat.Prime 737857 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_777901 : Nat.Prime 777901 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_799093 : Nat.Prime 799093 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_850943 : Nat.Prime 850943 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_905621 : Nat.Prime 905621 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_936511 : Nat.Prime 936511 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_965953 : Nat.Prime 965953 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_976109 : Nat.Prime 976109 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1103561 : Nat.Prime 1103561 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1115767 : Nat.Prime 1115767 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1159421 : Nat.Prime 1159421 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1163177 : Nat.Prime 1163177 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1195237 : Nat.Prime 1195237 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1276313 : Nat.Prime 1276313 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1293757 : Nat.Prime 1293757 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1313057 : Nat.Prime 1313057 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1415629 : Nat.Prime 1415629 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1417463 : Nat.Prime 1417463 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1418689 : Nat.Prime 1418689 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1454851 : Nat.Prime 1454851 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1468673 : Nat.Prime 1468673 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1481927 : Nat.Prime 1481927 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1527061 : Nat.Prime 1527061 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1618139 : Nat.Prime 1618139 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1685779 : Nat.Prime 1685779 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1768343 : Nat.Prime 1768343 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1824349 : Nat.Prime 1824349 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_1845769 : Nat.Prime 1845769 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2125553 : Nat.Prime 2125553 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2197603 : Nat.Prime 2197603 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2257861 : Nat.Prime 2257861 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2352247 : Nat.Prime 2352247 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2548127 : Nat.Prime 2548127 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2686573 : Nat.Prime 2686573 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2757191 : Nat.Prime 2757191 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2798639 : Nat.Prime 2798639 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_2864761 : Nat.Prime 2864761 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3150877 : Nat.Prime 3150877 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3176441 : Nat.Prime 3176441 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3210877 : Nat.Prime 3210877 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3251653 : Nat.Prime 3251653 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3308507 : Nat.Prime 3308507 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3344441 : Nat.Prime 3344441 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3638473 : Nat.Prime 3638473 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3641171 : Nat.Prime 3641171 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3662753 : Nat.Prime 3662753 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_3794299 : Nat.Prime 3794299 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4044331 : Nat.Prime 4044331 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4079143 : Nat.Prime 4079143 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4248259 : Nat.Prime 4248259 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4332479 : Nat.Prime 4332479 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_4482059 : Nat.Prime 4482059 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5081159 : Nat.Prime 5081159 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5244739 : Nat.Prime 5244739 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5354117 : Nat.Prime 5354117 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5643509 : Nat.Prime 5643509 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5742577 : Nat.Prime 5742577 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_5791081 : Nat.Prime 5791081 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6405131 : Nat.Prime 6405131 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6583277 : Nat.Prime 6583277 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6677597 : Nat.Prime 6677597 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6823183 : Nat.Prime 6823183 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6932221 : Nat.Prime 6932221 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_6980681 : Nat.Prime 6980681 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7026919 : Nat.Prime 7026919 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7165889 : Nat.Prime 7165889 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7363201 : Nat.Prime 7363201 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7368631 : Nat.Prime 7368631 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7702103 : Nat.Prime 7702103 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7711009 : Nat.Prime 7711009 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7720331 : Nat.Prime 7720331 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7845611 : Nat.Prime 7845611 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_7974227 : Nat.Prime 7974227 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_8851553 : Nat.Prime 8851553 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_8884129 : Nat.Prime 8884129 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_8939431 : Nat.Prime 8939431 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9000223 : Nat.Prime 9000223 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9082093 : Nat.Prime 9082093 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9861349 : Nat.Prime 9861349 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_9994261 : Nat.Prime 9994261 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_10046719 : Nat.Prime 10046719 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_10605079 : Nat.Prime 10605079 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_10655123 : Nat.Prime 10655123 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_11454329 : Nat.Prime 11454329 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_12102001 : Nat.Prime 12102001 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_12186047 : Nat.Prime 12186047 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_14498713 : Nat.Prime 14498713 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_15071873 : Nat.Prime 15071873 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_16720919 : Nat.Prime 16720919 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_17501417 : Nat.Prime 17501417 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_17886683 : Nat.Prime 17886683 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_18229217 : Nat.Prime 18229217 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_19363739 : Nat.Prime 19363739 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_20750447 : Nat.Prime 20750447 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_21773369 : Nat.Prime 21773369 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_21783529 : Nat.Prime 21783529 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_22470857 : Nat.Prime 22470857 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_24595171 : Nat.Prime 24595171 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_25449551 : Nat.Prime 25449551 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_27560623 : Nat.Prime 27560623 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_29705267 : Nat.Prime 29705267 := by
  norm_num

private theorem prime_oneHundredFortyOneEI_30744179 : Nat.Prime 30744179 := by
  apply lucas_primality 30744179 (2 : ZMod 30744179)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (374929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (374929, 1)] : List FactorBlock).map factorBlockValue).prod) = 30744179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_41
      · exact prime_oneHundredFortyOneEI_374929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30744179) ^ 15372089 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30744179) ^ 749858 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30744179) ^ 82 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_31428107 : Nat.Prime 31428107 := by
  apply lucas_primality 31428107 (2 : ZMod 31428107)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (215261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (215261, 1)] : List FactorBlock).map factorBlockValue).prod) = 31428107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_73
      · exact prime_oneHundredFortyOneEI_215261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31428107) ^ 15714053 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31428107) ^ 430522 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31428107) ^ 146 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_35366861 : Nat.Prime 35366861 := by
  apply lucas_primality 35366861 (2 : ZMod 35366861)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1768343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1768343, 1)] : List FactorBlock).map factorBlockValue).prod) = 35366861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_1768343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35366861) ^ 17683430 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 35366861) ^ 7073372 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 35366861) ^ 20 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_52033081 : Nat.Prime 52033081 := by
  apply lucas_primality 52033081 (41 : ZMod 52033081)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (39419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (39419, 1)] : List FactorBlock).map factorBlockValue).prod) = 52033081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_39419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 52033081) ^ 26016540 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (41 : ZMod 52033081) ^ 17344360 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (41 : ZMod 52033081) ^ 10406616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (41 : ZMod 52033081) ^ 4730280 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (41 : ZMod 52033081) ^ 1320 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_53420777 : Nat.Prime 53420777 := by
  apply lucas_primality 53420777 (3 : ZMod 53420777)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6677597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6677597, 1)] : List FactorBlock).map factorBlockValue).prod) = 53420777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_6677597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 53420777) ^ 26710388 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 53420777) ^ 8 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_57519949 : Nat.Prime 57519949 := by
  apply lucas_primality 57519949 (2 : ZMod 57519949)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1879, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1879, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 57519949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_1879
      · exact prime_oneHundredFortyOneEI_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57519949) ^ 28759974 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57519949) ^ 19173316 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57519949) ^ 30612 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57519949) ^ 22548 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_59308979 : Nat.Prime 59308979 := by
  apply lucas_primality 59308979 (2 : ZMod 59308979)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (357283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (357283, 1)] : List FactorBlock).map factorBlockValue).prod) = 59308979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_83
      · exact prime_oneHundredFortyOneEI_357283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59308979) ^ 29654489 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59308979) ^ 714566 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59308979) ^ 166 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_61488359 : Nat.Prime 61488359 := by
  apply lucas_primality 61488359 (7 : ZMod 61488359)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30744179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30744179, 1)] : List FactorBlock).map factorBlockValue).prod) = 61488359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_30744179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 61488359) ^ 30744179 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 61488359) ^ 2 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_64056061 : Nat.Prime 64056061 := by
  apply lucas_primality 64056061 (2 : ZMod 64056061)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (355867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (355867, 1)] : List FactorBlock).map factorBlockValue).prod) = 64056061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_355867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64056061) ^ 32028030 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 64056061) ^ 21352020 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 64056061) ^ 12811212 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 64056061) ^ 180 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_64419863 : Nat.Prime 64419863 := by
  apply lucas_primality 64419863 (5 : ZMod 64419863)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (71, 1), (34897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (71, 1), (34897, 1)] : List FactorBlock).map factorBlockValue).prod) = 64419863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_71
      · exact prime_oneHundredFortyOneEI_34897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64419863) ^ 32209931 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 64419863) ^ 4955374 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 64419863) ^ 907322 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 64419863) ^ 1846 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_66479239 : Nat.Prime 66479239 := by
  apply lucas_primality 66479239 (3 : ZMod 66479239)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (397, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (397, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 66479239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_397
      · exact prime_oneHundredFortyOneEI_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66479239) ^ 33239619 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66479239) ^ 22159746 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66479239) ^ 9497034 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66479239) ^ 167454 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66479239) ^ 150066 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_67436071 : Nat.Prime 67436071 := by
  apply lucas_primality 67436071 (3 : ZMod 67436071)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (47, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (47, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 67436071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67436071) ^ 33718035 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 67436071) ^ 22478690 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 67436071) ^ 13487214 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 67436071) ^ 5187390 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 67436071) ^ 1434810 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 67436071) ^ 238290 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_84047869 : Nat.Prime 84047869 := by
  apply lucas_primality 84047869 (2 : ZMod 84047869)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 6), (19, 1), (37, 1), (41, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 6), (19, 1), (37, 1), (41, 1)] : List FactorBlock).map factorBlockValue).prod) = 84047869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_41
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84047869) ^ 42023934 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 84047869) ^ 28015956 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 84047869) ^ 4423572 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 84047869) ^ 2271564 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 84047869) ^ 2049948 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_86208121 : Nat.Prime 86208121 := by
  apply lucas_primality 86208121 (7 : ZMod 86208121)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (43, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (43, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod) = 86208121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_5569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 86208121) ^ 43104060 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 86208121) ^ 28736040 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 86208121) ^ 17241624 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 86208121) ^ 2004840 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 86208121) ^ 15480 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_88610993 : Nat.Prime 88610993 := by
  apply lucas_primality 88610993 (3 : ZMod 88610993)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1427, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1427, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) = 88610993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1427
      · exact prime_oneHundredFortyOneEI_3881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 88610993) ^ 44305496 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88610993) ^ 62096 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88610993) ^ 22832 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_94405303 : Nat.Prime 94405303 := by
  apply lucas_primality 94405303 (3 : ZMod 94405303)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5244739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5244739, 1)] : List FactorBlock).map factorBlockValue).prod) = 94405303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5244739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94405303) ^ 47202651 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 94405303) ^ 31468434 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 94405303) ^ 18 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_98783837 : Nat.Prime 98783837 := by
  apply lucas_primality 98783837 (2 : ZMod 98783837)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271, 1), (91129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271, 1), (91129, 1)] : List FactorBlock).map factorBlockValue).prod) = 98783837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_271
      · exact prime_oneHundredFortyOneEI_91129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98783837) ^ 49391918 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 98783837) ^ 364516 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 98783837) ^ 1084 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_99094031 : Nat.Prime 99094031 := by
  apply lucas_primality 99094031 (7 : ZMod 99094031)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1415629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1415629, 1)] : List FactorBlock).map factorBlockValue).prod) = 99094031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_1415629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 99094031) ^ 49547015 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 99094031) ^ 19818806 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 99094031) ^ 14156290 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 99094031) ^ 70 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_110242493 : Nat.Prime 110242493 := by
  apply lucas_primality 110242493 (2 : ZMod 110242493)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (27560623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (27560623, 1)] : List FactorBlock).map factorBlockValue).prod) = 110242493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_27560623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 110242493) ^ 55121246 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 110242493) ^ 4 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_111234419 : Nat.Prime 111234419 := by
  apply lucas_primality 111234419 (2 : ZMod 111234419)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (519787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (519787, 1)] : List FactorBlock).map factorBlockValue).prod) = 111234419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_107
      · exact prime_oneHundredFortyOneEI_519787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111234419) ^ 55617209 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111234419) ^ 1039574 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111234419) ^ 214 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_115129349 : Nat.Prime 115129349 := by
  apply lucas_primality 115129349 (2 : ZMod 115129349)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (777901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (777901, 1)] : List FactorBlock).map factorBlockValue).prod) = 115129349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_777901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115129349) ^ 57564674 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 115129349) ^ 3111604 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 115129349) ^ 148 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_127540513 : Nat.Prime 127540513 := by
  apply lucas_primality 127540513 (10 : ZMod 127540513)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (127, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (127, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 127540513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_127
      · exact prime_oneHundredFortyOneEI_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 127540513) ^ 63770256 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 127540513) ^ 42513504 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 127540513) ^ 11594592 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 127540513) ^ 1004256 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 127540513) ^ 402336 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_130955939 : Nat.Prime 130955939 := by
  apply lucas_primality 130955939 (2 : ZMod 130955939)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2257861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2257861, 1)] : List FactorBlock).map factorBlockValue).prod) = 130955939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_29
      · exact prime_oneHundredFortyOneEI_2257861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 130955939) ^ 65477969 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 130955939) ^ 4515722 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 130955939) ^ 58 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_135956993 : Nat.Prime 135956993 := by
  apply lucas_primality 135956993 (3 : ZMod 135956993)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (265541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (265541, 1)] : List FactorBlock).map factorBlockValue).prod) = 135956993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_265541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 135956993) ^ 67978496 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135956993) ^ 512 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_148644523 : Nat.Prime 148644523 := by
  apply lucas_primality 148644523 (3 : ZMod 148644523)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (439, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (439, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 148644523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_439
      · exact prime_oneHundredFortyOneEI_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 148644523) ^ 74322261 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 148644523) ^ 49548174 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 148644523) ^ 11434194 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 148644523) ^ 338598 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 148644523) ^ 102726 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_166143917 : Nat.Prime 166143917 := by
  apply lucas_primality 166143917 (2 : ZMod 166143917)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (965953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (965953, 1)] : List FactorBlock).map factorBlockValue).prod) = 166143917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_965953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 166143917) ^ 83071958 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 166143917) ^ 3863812 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 166143917) ^ 172 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_169632763 : Nat.Prime 169632763 := by
  apply lucas_primality 169632763 (2 : ZMod 169632763)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1217, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1217, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) = 169632763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_1217
      · exact prime_oneHundredFortyOneEI_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 169632763) ^ 84816381 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 169632763) ^ 56544254 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 169632763) ^ 13048674 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 169632763) ^ 139386 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 169632763) ^ 94926 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_190240849 : Nat.Prime 190240849 := by
  apply lucas_primality 190240849 (11 : ZMod 190240849)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (79, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (79, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) = 190240849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_79
      · exact prime_oneHundredFortyOneEI_2389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 190240849) ^ 95120424 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 190240849) ^ 63413616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 190240849) ^ 27177264 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 190240849) ^ 2408112 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 190240849) ^ 79632 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_205870607 : Nat.Prime 205870607 := by
  apply lucas_primality 205870607 (5 : ZMod 205870607)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (1123, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (1123, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) = 205870607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_71
      · exact prime_oneHundredFortyOneEI_1123
      · exact prime_oneHundredFortyOneEI_1291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 205870607) ^ 102935303 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 205870607) ^ 2899586 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 205870607) ^ 183322 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 205870607) ^ 159466 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_216848939 : Nat.Prime 216848939 := by
  apply lucas_primality 216848939 (2 : ZMod 216848939)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (149, 1), (38299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (149, 1), (38299, 1)] : List FactorBlock).map factorBlockValue).prod) = 216848939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_149
      · exact prime_oneHundredFortyOneEI_38299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 216848939) ^ 108424469 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 216848939) ^ 11413102 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 216848939) ^ 1455362 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 216848939) ^ 5662 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_220614671 : Nat.Prime 220614671 := by
  apply lucas_primality 220614671 (7 : ZMod 220614671)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (103, 1), (214189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (103, 1), (214189, 1)] : List FactorBlock).map factorBlockValue).prod) = 220614671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_103
      · exact prime_oneHundredFortyOneEI_214189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 220614671) ^ 110307335 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 220614671) ^ 44122934 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 220614671) ^ 2141890 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 220614671) ^ 1030 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_222162233 : Nat.Prime 222162233 := by
  apply lucas_primality 222162233 (3 : ZMod 222162233)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (349, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (349, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 222162233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_349
      · exact prime_oneHundredFortyOneEI_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 222162233) ^ 111081116 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 222162233) ^ 4726856 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 222162233) ^ 636568 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 222162233) ^ 131224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_241558753 : Nat.Prime 241558753 := by
  apply lucas_primality 241558753 (5 : ZMod 241558753)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (73, 1), (34469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (73, 1), (34469, 1)] : List FactorBlock).map factorBlockValue).prod) = 241558753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_73
      · exact prime_oneHundredFortyOneEI_34469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 241558753) ^ 120779376 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 241558753) ^ 80519584 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 241558753) ^ 3309024 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 241558753) ^ 7008 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_271913987 : Nat.Prime 271913987 := by
  apply lucas_primality 271913987 (2 : ZMod 271913987)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (135956993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (135956993, 1)] : List FactorBlock).map factorBlockValue).prod) = 271913987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_135956993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 271913987) ^ 135956993 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 271913987) ^ 2 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_275113357 : Nat.Prime 275113357 := by
  apply lucas_primality 275113357 (2 : ZMod 275113357)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (71, 1), (163, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (71, 1), (163, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 275113357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_71
      · exact prime_oneHundredFortyOneEI_163
      · exact prime_oneHundredFortyOneEI_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 275113357) ^ 137556678 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 275113357) ^ 91704452 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 275113357) ^ 39301908 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 275113357) ^ 3874836 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 275113357) ^ 1687812 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 275113357) ^ 972132 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_315732119 : Nat.Prime 315732119 := by
  apply lucas_primality 315732119 (17 : ZMod 315732119)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (137, 2), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (137, 2), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 315732119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_137
      · exact prime_oneHundredFortyOneEI_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 315732119) ^ 157866059 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 315732119) ^ 24287086 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 315732119) ^ 2304614 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 315732119) ^ 487994 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_333439321 : Nat.Prime 333439321 := by
  apply lucas_primality 333439321 (11 : ZMod 333439321)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (163, 1), (17047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (163, 1), (17047, 1)] : List FactorBlock).map factorBlockValue).prod) = 333439321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_163
      · exact prime_oneHundredFortyOneEI_17047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 333439321) ^ 166719660 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 333439321) ^ 111146440 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 333439321) ^ 66687864 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 333439321) ^ 2045640 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 333439321) ^ 19560 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_342916003 : Nat.Prime 342916003 := by
  apply lucas_primality 342916003 (5 : ZMod 342916003)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (127, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (127, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) = 342916003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_127
      · exact prime_oneHundredFortyOneEI_1049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 342916003) ^ 171458001 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 342916003) ^ 114305334 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 342916003) ^ 31174182 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 342916003) ^ 26378154 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 342916003) ^ 2700126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 342916003) ^ 326898 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_416871883 : Nat.Prime 416871883 := by
  apply lucas_primality 416871883 (2 : ZMod 416871883)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3308507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3308507, 1)] : List FactorBlock).map factorBlockValue).prod) = 416871883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_3308507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416871883) ^ 208435941 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 416871883) ^ 138957294 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 416871883) ^ 59553126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 416871883) ^ 126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_504826249 : Nat.Prime 504826249 := by
  apply lucas_primality 504826249 (31 : ZMod 504826249)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (447541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (447541, 1)] : List FactorBlock).map factorBlockValue).prod) = 504826249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_447541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 504826249) ^ 252413124 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (31 : ZMod 504826249) ^ 168275416 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (31 : ZMod 504826249) ^ 10740984 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (31 : ZMod 504826249) ^ 1128 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_542575261 : Nat.Prime 542575261 := by
  apply lucas_primality 542575261 (2 : ZMod 542575261)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 1), (111641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 1), (111641, 1)] : List FactorBlock).map factorBlockValue).prod) = 542575261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_111641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 542575261) ^ 271287630 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 542575261) ^ 180858420 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 542575261) ^ 108515052 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 542575261) ^ 4860 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_542879531 : Nat.Prime 542879531 := by
  apply lucas_primality 542879531 (6 : ZMod 542879531)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (53, 1), (89, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (53, 1), (89, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 542879531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_53
      · exact prime_oneHundredFortyOneEI_89
      · exact prime_oneHundredFortyOneEI_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 542879531) ^ 271439765 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 542879531) ^ 108575906 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 542879531) ^ 31934090 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 542879531) ^ 10243010 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 542879531) ^ 6099770 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 542879531) ^ 801890 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_591867319 : Nat.Prime 591867319 := by
  apply lucas_primality 591867319 (12 : ZMod 591867319)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (380867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (380867, 1)] : List FactorBlock).map factorBlockValue).prod) = 591867319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_380867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 591867319) ^ 295933659 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (12 : ZMod 591867319) ^ 197289106 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (12 : ZMod 591867319) ^ 84552474 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (12 : ZMod 591867319) ^ 15996414 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (12 : ZMod 591867319) ^ 1554 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_61
      · exact prime_oneHundredFortyOneEI_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_678531053 : Nat.Prime 678531053 := by
  apply lucas_primality 678531053 (2 : ZMod 678531053)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (169632763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (169632763, 1)] : List FactorBlock).map factorBlockValue).prod) = 678531053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_169632763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 678531053) ^ 339265526 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 678531053) ^ 4 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_17203
      · exact prime_oneHundredFortyOneEI_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_720952987 : Nat.Prime 720952987 := by
  apply lucas_primality 720952987 (14 : ZMod 720952987)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (19, 1), (23, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (19, 1), (23, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) = 720952987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_1627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 720952987) ^ 360476493 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 720952987) ^ 240317662 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 720952987) ^ 55457922 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 720952987) ^ 37944894 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 720952987) ^ 31345782 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 720952987) ^ 443118 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_735463373 : Nat.Prime 735463373 := by
  apply lucas_primality 735463373 (3 : ZMod 735463373)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1973, 1), (13313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1973, 1), (13313, 1)] : List FactorBlock).map factorBlockValue).prod) = 735463373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_1973
      · exact prime_oneHundredFortyOneEI_13313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 735463373) ^ 367731686 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 735463373) ^ 105066196 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 735463373) ^ 372764 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 735463373) ^ 55244 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_775037171 : Nat.Prime 775037171 := by
  apply lucas_primality 775037171 (2 : ZMod 775037171)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (4079143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (4079143, 1)] : List FactorBlock).map factorBlockValue).prod) = 775037171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_4079143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 775037171) ^ 387518585 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 775037171) ^ 155007434 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 775037171) ^ 40791430 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 775037171) ^ 190 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_899645833 : Nat.Prime 899645833 := by
  apply lucas_primality 899645833 (10 : ZMod 899645833)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (433, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (433, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) = 899645833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_433
      · exact prime_oneHundredFortyOneEI_9619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 899645833) ^ 449822916 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 899645833) ^ 299881944 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 899645833) ^ 2077704 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 899645833) ^ 93528 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_910011247 : Nat.Prime 910011247 := by
  apply lucas_primality 910011247 (3 : ZMod 910011247)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (1417463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (1417463, 1)] : List FactorBlock).map factorBlockValue).prod) = 910011247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_107
      · exact prime_oneHundredFortyOneEI_1417463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910011247) ^ 455005623 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 910011247) ^ 303337082 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 910011247) ^ 8504778 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 910011247) ^ 642 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_938829751 : Nat.Prime 938829751 := by
  apply lucas_primality 938829751 (3 : ZMod 938829751)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (43, 2), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (43, 2), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 938829751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 938829751) ^ 469414875 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 938829751) ^ 312943250 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 938829751) ^ 187765950 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 938829751) ^ 21833250 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 938829751) ^ 1386750 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_963819161 : Nat.Prime 963819161 := by
  apply lucas_primality 963819161 (3 : ZMod 963819161)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (97, 1), (248407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (97, 1), (248407, 1)] : List FactorBlock).map factorBlockValue).prod) = 963819161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_97
      · exact prime_oneHundredFortyOneEI_248407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 963819161) ^ 481909580 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 963819161) ^ 192763832 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 963819161) ^ 9936280 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 963819161) ^ 3880 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_999087031 : Nat.Prime 999087031 := by
  apply lucas_primality 999087031 (3 : ZMod 999087031)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (263, 1), (42209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (263, 1), (42209, 1)] : List FactorBlock).map factorBlockValue).prod) = 999087031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_263
      · exact prime_oneHundredFortyOneEI_42209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 999087031) ^ 499543515 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 999087031) ^ 333029010 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 999087031) ^ 199817406 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 999087031) ^ 3798810 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 999087031) ^ 23670 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1063331917 : Nat.Prime 1063331917 := by
  apply lucas_primality 1063331917 (6 : ZMod 1063331917)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (88610993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (88610993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063331917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_88610993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1063331917) ^ 531665958 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1063331917) ^ 354443972 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1063331917) ^ 12 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1085759063 : Nat.Prime 1085759063 := by
  apply lucas_primality 1085759063 (5 : ZMod 1085759063)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (542879531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (542879531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085759063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_542879531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1085759063) ^ 542879531 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1085759063) ^ 2 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1188960133 : Nat.Prime 1188960133 := by
  apply lucas_primality 1188960133 (2 : ZMod 1188960133)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (641, 1), (154571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (641, 1), (154571, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188960133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_641
      · exact prime_oneHundredFortyOneEI_154571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1188960133) ^ 594480066 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188960133) ^ 396320044 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188960133) ^ 1854852 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188960133) ^ 7692 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1269710921 : Nat.Prime 1269710921 := by
  apply lucas_primality 1269710921 (3 : ZMod 1269710921)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (439, 1), (72307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (439, 1), (72307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1269710921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_439
      · exact prime_oneHundredFortyOneEI_72307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1269710921) ^ 634855460 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269710921) ^ 253942184 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269710921) ^ 2892280 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269710921) ^ 17560 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1329151337 : Nat.Prime 1329151337 := by
  apply lucas_primality 1329151337 (3 : ZMod 1329151337)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (166143917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (166143917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1329151337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_166143917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1329151337) ^ 664575668 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1329151337) ^ 8 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1351909193 : Nat.Prime 1351909193 := by
  apply lucas_primality 1351909193 (3 : ZMod 1351909193)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (73, 1), (173, 1), (13381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (73, 1), (173, 1), (13381, 1)] : List FactorBlock).map factorBlockValue).prod) = 1351909193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_73
      · exact prime_oneHundredFortyOneEI_173
      · exact prime_oneHundredFortyOneEI_13381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1351909193) ^ 675954596 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351909193) ^ 18519304 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351909193) ^ 7814504 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351909193) ^ 101032 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1543847677 : Nat.Prime 1543847677 := by
  apply lucas_primality 1543847677 (6 : ZMod 1543847677)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (799093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (799093, 1)] : List FactorBlock).map factorBlockValue).prod) = 1543847677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_799093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1543847677) ^ 771923838 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1543847677) ^ 514615892 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1543847677) ^ 220549668 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1543847677) ^ 67123812 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1543847677) ^ 1932 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1662843419 : Nat.Prime 1662843419 := by
  apply lucas_primality 1662843419 (2 : ZMod 1662843419)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (22470857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (22470857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1662843419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_22470857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1662843419) ^ 831421709 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662843419) ^ 44941714 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662843419) ^ 74 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2000635927 : Nat.Prime 2000635927 := by
  apply lucas_primality 2000635927 (5 : ZMod 2000635927)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (333439321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (333439321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2000635927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_333439321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2000635927) ^ 1000317963 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2000635927) ^ 666878642 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2000635927) ^ 6 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2173514117 : Nat.Prime 2173514117 := by
  apply lucas_primality 2173514117 (2 : ZMod 2173514117)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (487, 1), (1115767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (487, 1), (1115767, 1)] : List FactorBlock).map factorBlockValue).prod) = 2173514117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_487
      · exact prime_oneHundredFortyOneEI_1115767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2173514117) ^ 1086757058 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2173514117) ^ 4463068 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2173514117) ^ 1948 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2367469277 : Nat.Prime 2367469277 := by
  apply lucas_primality 2367469277 (2 : ZMod 2367469277)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (591867319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (591867319, 1)] : List FactorBlock).map factorBlockValue).prod) = 2367469277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_591867319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2367469277) ^ 1183734638 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2367469277) ^ 4 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2434103017 : Nat.Prime 2434103017 := by
  apply lucas_primality 2434103017 (7 : ZMod 2434103017)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (53, 1), (51719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (53, 1), (51719, 1)] : List FactorBlock).map factorBlockValue).prod) = 2434103017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_53
      · exact prime_oneHundredFortyOneEI_51719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2434103017) ^ 1217051508 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2434103017) ^ 811367672 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2434103017) ^ 65786568 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2434103017) ^ 45926472 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2434103017) ^ 47064 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2801620963 : Nat.Prime 2801620963 := by
  apply lucas_primality 2801620963 (7 : ZMod 2801620963)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (3176441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (3176441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2801620963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_3176441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2801620963) ^ 1400810481 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2801620963) ^ 933873654 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2801620963) ^ 400231566 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2801620963) ^ 882 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2858116181 : Nat.Prime 2858116181 := by
  apply lucas_primality 2858116181 (2 : ZMod 2858116181)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (101, 2), (14009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (101, 2), (14009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2858116181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_101
      · exact prime_oneHundredFortyOneEI_14009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2858116181) ^ 1429058090 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858116181) ^ 571623236 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858116181) ^ 28298180 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858116181) ^ 204020 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3077025157 : Nat.Prime 3077025157 := by
  apply lucas_primality 3077025157 (2 : ZMod 3077025157)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (2757191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (2757191, 1)] : List FactorBlock).map factorBlockValue).prod) = 3077025157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_2757191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3077025157) ^ 1538512578 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077025157) ^ 1025675052 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077025157) ^ 99258876 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077025157) ^ 1116 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3390934867 : Nat.Prime 3390934867 := by
  apply lucas_primality 3390934867 (2 : ZMod 3390934867)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (71, 1), (283, 1), (2557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (71, 1), (283, 1), (2557, 1)] : List FactorBlock).map factorBlockValue).prod) = 3390934867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_71
      · exact prime_oneHundredFortyOneEI_283
      · exact prime_oneHundredFortyOneEI_2557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3390934867) ^ 1695467433 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3390934867) ^ 1130311622 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3390934867) ^ 308266806 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3390934867) ^ 47759646 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3390934867) ^ 11982102 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3390934867) ^ 1326138 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3521141011 : Nat.Prime 3521141011 := by
  apply lucas_primality 3521141011 (14 : ZMod 3521141011)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (223, 1), (58481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (223, 1), (58481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3521141011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_223
      · exact prime_oneHundredFortyOneEI_58481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 3521141011) ^ 1760570505 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 3521141011) ^ 1173713670 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 3521141011) ^ 704228202 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 3521141011) ^ 15789870 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 3521141011) ^ 60210 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3689301541 : Nat.Prime 3689301541 := by
  apply lucas_primality 3689301541 (2 : ZMod 3689301541)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61488359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61488359, 1)] : List FactorBlock).map factorBlockValue).prod) = 3689301541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_61488359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3689301541) ^ 1844650770 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689301541) ^ 1229767180 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689301541) ^ 737860308 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689301541) ^ 60 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3951228503 : Nat.Prime 3951228503 := by
  apply lucas_primality 3951228503 (5 : ZMod 3951228503)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (8939431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (8939431, 1)] : List FactorBlock).map factorBlockValue).prod) = 3951228503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_8939431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3951228503) ^ 1975614251 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951228503) ^ 303940654 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951228503) ^ 232425206 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951228503) ^ 442 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4230241207 : Nat.Prime 4230241207 := by
  apply lucas_primality 4230241207 (6 : ZMod 4230241207)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (239, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (239, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) = 4230241207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_239
      · exact prime_oneHundredFortyOneEI_9133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4230241207) ^ 2115120603 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4230241207) ^ 1410080402 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4230241207) ^ 248837718 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4230241207) ^ 222644274 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4230241207) ^ 17699754 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4230241207) ^ 463182 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4454125997 : Nat.Prime 4454125997 := by
  apply lucas_primality 4454125997 (2 : ZMod 4454125997)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (23, 1), (2548127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (23, 1), (2548127, 1)] : List FactorBlock).map factorBlockValue).prod) = 4454125997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_2548127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4454125997) ^ 2227062998 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4454125997) ^ 234427684 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4454125997) ^ 193657652 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4454125997) ^ 1748 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4570401233 : Nat.Prime 4570401233 := by
  apply lucas_primality 4570401233 (3 : ZMod 4570401233)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4003, 1), (71359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4003, 1), (71359, 1)] : List FactorBlock).map factorBlockValue).prod) = 4570401233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_4003
      · exact prime_oneHundredFortyOneEI_71359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4570401233) ^ 2285200616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4570401233) ^ 1141744 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4570401233) ^ 64048 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4780953523 : Nat.Prime 4780953523 := by
  apply lucas_primality 4780953523 (3 : ZMod 4780953523)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (3638473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (3638473, 1)] : List FactorBlock).map factorBlockValue).prod) = 4780953523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_73
      · exact prime_oneHundredFortyOneEI_3638473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4780953523) ^ 2390476761 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4780953523) ^ 1593651174 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4780953523) ^ 65492514 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4780953523) ^ 1314 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6493444021 : Nat.Prime 6493444021 := by
  apply lucas_primality 6493444021 (14 : ZMod 6493444021)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (911, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (911, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod) = 6493444021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_911
      · exact prime_oneHundredFortyOneEI_5657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 6493444021) ^ 3246722010 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 6493444021) ^ 2164481340 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 6493444021) ^ 1298688804 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 6493444021) ^ 927634860 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 6493444021) ^ 7127820 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 6493444021) ^ 1147860 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6560117423 : Nat.Prime 6560117423 := by
  apply lucas_primality 6560117423 (5 : ZMod 6560117423)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5657, 1), (30517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5657, 1), (30517, 1)] : List FactorBlock).map factorBlockValue).prod) = 6560117423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_5657
      · exact prime_oneHundredFortyOneEI_30517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6560117423) ^ 3280058711 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6560117423) ^ 345269338 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6560117423) ^ 1159646 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6560117423) ^ 214966 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_7872311467 : Nat.Prime 7872311467 := by
  apply lucas_primality 7872311467 (13 : ZMod 7872311467)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (467, 1), (936511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (467, 1), (936511, 1)] : List FactorBlock).map factorBlockValue).prod) = 7872311467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_467
      · exact prime_oneHundredFortyOneEI_936511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 7872311467) ^ 3936155733 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7872311467) ^ 2624103822 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7872311467) ^ 16857198 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7872311467) ^ 8406 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_8061299567 : Nat.Prime 8061299567 := by
  apply lucas_primality 8061299567 (5 : ZMod 8061299567)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7121, 1), (566023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7121, 1), (566023, 1)] : List FactorBlock).map factorBlockValue).prod) = 8061299567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7121
      · exact prime_oneHundredFortyOneEI_566023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8061299567) ^ 4030649783 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8061299567) ^ 1132046 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8061299567) ^ 14242 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_8111455159 : Nat.Prime 8111455159 := by
  apply lucas_primality 8111455159 (6 : ZMod 8111455159)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1351909193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1351909193, 1)] : List FactorBlock).map factorBlockValue).prod) = 8111455159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_1351909193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 8111455159) ^ 4055727579 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8111455159) ^ 2703818386 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8111455159) ^ 6 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_8276041747 : Nat.Prime 8276041747 := by
  apply lucas_primality 8276041747 (2 : ZMod 8276041747)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (59, 1), (97, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (59, 1), (97, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 8276041747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_59
      · exact prime_oneHundredFortyOneEI_97
      · exact prime_oneHundredFortyOneEI_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8276041747) ^ 4138020873 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8276041747) ^ 2758680582 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8276041747) ^ 1182291678 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8276041747) ^ 359827902 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8276041747) ^ 140271894 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8276041747) ^ 85320018 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8276041747) ^ 16585254 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_10343781673 : Nat.Prime 10343781673 := by
  apply lucas_primality 10343781673 (10 : ZMod 10343781673)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (137, 1), (449417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (137, 1), (449417, 1)] : List FactorBlock).map factorBlockValue).prod) = 10343781673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_137
      · exact prime_oneHundredFortyOneEI_449417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10343781673) ^ 5171890836 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 10343781673) ^ 3447927224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 10343781673) ^ 1477683096 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 10343781673) ^ 75502056 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 10343781673) ^ 23016 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_10633210697 : Nat.Prime 10633210697 := by
  apply lucas_primality 10633210697 (3 : ZMod 10633210697)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1329151337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1329151337, 1)] : List FactorBlock).map factorBlockValue).prod) = 10633210697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1329151337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 10633210697) ^ 5316605348 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10633210697) ^ 8 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_12253861993 : Nat.Prime 12253861993 := by
  apply lucas_primality 12253861993 (10 : ZMod 12253861993)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2683, 1), (190301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2683, 1), (190301, 1)] : List FactorBlock).map factorBlockValue).prod) = 12253861993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_2683
      · exact prime_oneHundredFortyOneEI_190301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 12253861993) ^ 6126930996 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 12253861993) ^ 4084620664 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 12253861993) ^ 4567224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 12253861993) ^ 64392 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_13444634219 : Nat.Prime 13444634219 := by
  apply lucas_primality 13444634219 (2 : ZMod 13444634219)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (216848939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (216848939, 1)] : List FactorBlock).map factorBlockValue).prod) = 13444634219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_216848939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13444634219) ^ 6722317109 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13444634219) ^ 433697878 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13444634219) ^ 62 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_18493829017 : Nat.Prime 18493829017 := by
  apply lucas_primality 18493829017 (10 : ZMod 18493829017)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (4567, 1), (12979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (4567, 1), (12979, 1)] : List FactorBlock).map factorBlockValue).prod) = 18493829017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_4567
      · exact prime_oneHundredFortyOneEI_12979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 18493829017) ^ 9246914508 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 18493829017) ^ 6164609672 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 18493829017) ^ 1422602232 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 18493829017) ^ 4049448 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 18493829017) ^ 1424904 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_21979914683 : Nat.Prime 21979914683 := by
  apply lucas_primality 21979914683 (2 : ZMod 21979914683)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (999087031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (999087031, 1)] : List FactorBlock).map factorBlockValue).prod) = 21979914683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_999087031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21979914683) ^ 10989957341 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21979914683) ^ 1998174062 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21979914683) ^ 22 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_24642674123 : Nat.Prime 24642674123 := by
  apply lucas_primality 24642674123 (2 : ZMod 24642674123)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (23, 1), (2864761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (23, 1), (2864761, 1)] : List FactorBlock).map factorBlockValue).prod) = 24642674123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_2864761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24642674123) ^ 12321337061 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24642674123) ^ 2240243102 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24642674123) ^ 1449569066 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24642674123) ^ 1071420614 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24642674123) ^ 8602 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_27783661253 : Nat.Prime 27783661253 := by
  apply lucas_primality 27783661253 (2 : ZMod 27783661253)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (67436071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (67436071, 1)] : List FactorBlock).map factorBlockValue).prod) = 27783661253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_103
      · exact prime_oneHundredFortyOneEI_67436071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27783661253) ^ 13891830626 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27783661253) ^ 269744284 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27783661253) ^ 412 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_31386441329 : Nat.Prime 31386441329 := by
  apply lucas_primality 31386441329 (3 : ZMod 31386441329)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (47, 1), (3794299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (47, 1), (3794299, 1)] : List FactorBlock).map factorBlockValue).prod) = 31386441329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_3794299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31386441329) ^ 15693220664 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 31386441329) ^ 2853312848 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 31386441329) ^ 667796624 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 31386441329) ^ 8272 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_40454534441 : Nat.Prime 40454534441 := by
  apply lucas_primality 40454534441 (3 : ZMod 40454534441)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (131, 1), (7720331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (131, 1), (7720331, 1)] : List FactorBlock).map factorBlockValue).prod) = 40454534441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_131
      · exact prime_oneHundredFortyOneEI_7720331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40454534441) ^ 20227267220 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40454534441) ^ 8090906888 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40454534441) ^ 308813240 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40454534441) ^ 5240 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_40656653749 : Nat.Prime 40656653749 := by
  apply lucas_primality 40656653749 (2 : ZMod 40656653749)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (113, 1), (9994261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (113, 1), (9994261, 1)] : List FactorBlock).map factorBlockValue).prod) = 40656653749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_113
      · exact prime_oneHundredFortyOneEI_9994261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40656653749) ^ 20328326874 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40656653749) ^ 13552217916 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40656653749) ^ 359793396 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40656653749) ^ 4068 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_44832096721 : Nat.Prime 44832096721 := by
  apply lucas_primality 44832096721 (14 : ZMod 44832096721)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (17, 1), (3662753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (17, 1), (3662753, 1)] : List FactorBlock).map factorBlockValue).prod) = 44832096721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_3662753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 44832096721) ^ 22416048360 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 44832096721) ^ 14944032240 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 44832096721) ^ 8966419344 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 44832096721) ^ 2637182160 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 44832096721) ^ 12240 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_54107721791 : Nat.Prime 54107721791 := by
  apply lucas_primality 54107721791 (7 : ZMod 54107721791)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (271, 1), (463, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (271, 1), (463, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod) = 54107721791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_29
      · exact prime_oneHundredFortyOneEI_271
      · exact prime_oneHundredFortyOneEI_463
      · exact prime_oneHundredFortyOneEI_1487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 54107721791) ^ 27053860895 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 54107721791) ^ 10821544358 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 54107721791) ^ 1865783510 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 54107721791) ^ 199659490 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 54107721791) ^ 116863330 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 54107721791) ^ 36387170 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_59184179693 : Nat.Prime 59184179693 := by
  apply lucas_primality 59184179693 (2 : ZMod 59184179693)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (23, 1), (571, 1), (9311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (23, 1), (571, 1), (9311, 1)] : List FactorBlock).map factorBlockValue).prod) = 59184179693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_571
      · exact prime_oneHundredFortyOneEI_9311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59184179693) ^ 29592089846 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59184179693) ^ 5380379972 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59184179693) ^ 2573225204 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59184179693) ^ 103650052 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59184179693) ^ 6356372 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_72745980917 : Nat.Prime 72745980917 := by
  apply lucas_primality 72745980917 (2 : ZMod 72745980917)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (47, 1), (3251653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (47, 1), (3251653, 1)] : List FactorBlock).map factorBlockValue).prod) = 72745980917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_3251653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72745980917) ^ 36372990458 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 72745980917) ^ 10392282988 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 72745980917) ^ 4279175348 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 72745980917) ^ 1547786828 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 72745980917) ^ 22372 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_80460304399 : Nat.Prime 80460304399 := by
  apply lucas_primality 80460304399 (3 : ZMod 80460304399)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (151, 1), (829, 1), (11903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (151, 1), (829, 1), (11903, 1)] : List FactorBlock).map factorBlockValue).prod) = 80460304399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_151
      · exact prime_oneHundredFortyOneEI_829
      · exact prime_oneHundredFortyOneEI_11903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 80460304399) ^ 40230152199 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80460304399) ^ 26820101466 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80460304399) ^ 532849698 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80460304399) ^ 97057062 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80460304399) ^ 6759666 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_80909068883 : Nat.Prime 80909068883 := by
  apply lucas_primality 80909068883 (2 : ZMod 80909068883)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40454534441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40454534441, 1)] : List FactorBlock).map factorBlockValue).prod) = 80909068883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_40454534441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 80909068883) ^ 40454534441 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 80909068883) ^ 2 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_89314544933 : Nat.Prime 89314544933 := by
  apply lucas_primality 89314544933 (2 : ZMod 89314544933)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (20599, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (20599, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) = 89314544933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_20599
      · exact prime_oneHundredFortyOneEI_47129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89314544933) ^ 44657272466 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 89314544933) ^ 3883241084 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 89314544933) ^ 4335868 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 89314544933) ^ 1895108 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_95461824379 : Nat.Prime 95461824379 := by
  apply lucas_primality 95461824379 (2 : ZMod 95461824379)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (101, 1), (113, 1), (82003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (101, 1), (113, 1), (82003, 1)] : List FactorBlock).map factorBlockValue).prod) = 95461824379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_101
      · exact prime_oneHundredFortyOneEI_113
      · exact prime_oneHundredFortyOneEI_82003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95461824379) ^ 47730912189 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 95461824379) ^ 31820608126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 95461824379) ^ 5615401434 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 95461824379) ^ 945166578 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 95461824379) ^ 844794906 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 95461824379) ^ 1164126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_113095616857 : Nat.Prime 113095616857 := by
  apply lucas_primality 113095616857 (5 : ZMod 113095616857)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1409, 1), (3344441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1409, 1), (3344441, 1)] : List FactorBlock).map factorBlockValue).prod) = 113095616857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_1409
      · exact prime_oneHundredFortyOneEI_3344441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 113095616857) ^ 56547808428 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 113095616857) ^ 37698538952 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 113095616857) ^ 80266584 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 113095616857) ^ 33816 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_150975436541 : Nat.Prime 150975436541 := by
  apply lucas_primality 150975436541 (2 : ZMod 150975436541)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2351, 1), (3210877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2351, 1), (3210877, 1)] : List FactorBlock).map factorBlockValue).prod) = 150975436541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_2351
      · exact prime_oneHundredFortyOneEI_3210877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 150975436541) ^ 75487718270 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 150975436541) ^ 30195087308 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 150975436541) ^ 64217540 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 150975436541) ^ 47020 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_153555001753 : Nat.Prime 153555001753 := by
  apply lucas_primality 153555001753 (10 : ZMod 153555001753)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (53, 1), (101, 1), (157, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (53, 1), (101, 1), (157, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 153555001753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_53
      · exact prime_oneHundredFortyOneEI_101
      · exact prime_oneHundredFortyOneEI_157
      · exact prime_oneHundredFortyOneEI_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 153555001753) ^ 76777500876 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 153555001753) ^ 51185000584 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 153555001753) ^ 6676304424 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 153555001753) ^ 2897264184 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 153555001753) ^ 1520346552 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 153555001753) ^ 978057336 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 153555001753) ^ 463912392 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_162428399957 : Nat.Prime 162428399957 := by
  apply lucas_primality 162428399957 (2 : ZMod 162428399957)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1367, 1), (29705267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1367, 1), (29705267, 1)] : List FactorBlock).map factorBlockValue).prod) = 162428399957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1367
      · exact prime_oneHundredFortyOneEI_29705267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 162428399957) ^ 81214199978 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 162428399957) ^ 118821068 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 162428399957) ^ 5468 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_162542185423 : Nat.Prime 162542185423 := by
  apply lucas_primality 162542185423 (3 : ZMod 162542185423)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (342916003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (342916003, 1)] : List FactorBlock).map factorBlockValue).prod) = 162542185423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_79
      · exact prime_oneHundredFortyOneEI_342916003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 162542185423) ^ 81271092711 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 162542185423) ^ 54180728474 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 162542185423) ^ 2057496018 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 162542185423) ^ 474 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_166701967519 : Nat.Prime 166701967519 := by
  apply lucas_primality 166701967519 (3 : ZMod 166701967519)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (27783661253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (27783661253, 1)] : List FactorBlock).map factorBlockValue).prod) = 166701967519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_27783661253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 166701967519) ^ 83350983759 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 166701967519) ^ 55567322506 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 166701967519) ^ 6 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_197095504523 : Nat.Prime 197095504523 := by
  apply lucas_primality 197095504523 (2 : ZMod 197095504523)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (971, 1), (14498713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (971, 1), (14498713, 1)] : List FactorBlock).map factorBlockValue).prod) = 197095504523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_971
      · exact prime_oneHundredFortyOneEI_14498713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197095504523) ^ 98547752261 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197095504523) ^ 28156500646 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197095504523) ^ 202981982 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197095504523) ^ 13594 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_208996911551 : Nat.Prime 208996911551 := by
  apply lucas_primality 208996911551 (14 : ZMod 208996911551)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (19, 1), (31428107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (19, 1), (31428107, 1)] : List FactorBlock).map factorBlockValue).prod) = 208996911551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_31428107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 208996911551) ^ 104498455775 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 208996911551) ^ 41799382310 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 208996911551) ^ 29856701650 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 208996911551) ^ 10999837450 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 208996911551) ^ 6650 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_239369471879 : Nat.Prime 239369471879 := by
  apply lucas_primality 239369471879 (13 : ZMod 239369471879)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2027, 1), (5701, 1), (10357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2027, 1), (5701, 1), (10357, 1)] : List FactorBlock).map factorBlockValue).prod) = 239369471879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_2027
      · exact prime_oneHundredFortyOneEI_5701
      · exact prime_oneHundredFortyOneEI_10357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 239369471879) ^ 119684735939 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 239369471879) ^ 118090514 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 239369471879) ^ 41987278 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 239369471879) ^ 23111854 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_239548603583 : Nat.Prime 239548603583 := by
  apply lucas_primality 239548603583 (5 : ZMod 239548603583)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (2129, 1), (677813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (2129, 1), (677813, 1)] : List FactorBlock).map factorBlockValue).prod) = 239548603583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_83
      · exact prime_oneHundredFortyOneEI_2129
      · exact prime_oneHundredFortyOneEI_677813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 239548603583) ^ 119774301791 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 239548603583) ^ 2886127754 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 239548603583) ^ 112516958 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 239548603583) ^ 353414 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_252518452973 : Nat.Prime 252518452973 := by
  apply lucas_primality 252518452973 (2 : ZMod 252518452973)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (521, 1), (529127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (521, 1), (529127, 1)] : List FactorBlock).map factorBlockValue).prod) = 252518452973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_229
      · exact prime_oneHundredFortyOneEI_521
      · exact prime_oneHundredFortyOneEI_529127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 252518452973) ^ 126259226486 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 252518452973) ^ 1102700668 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 252518452973) ^ 484680332 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 252518452973) ^ 477236 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_269293726253 : Nat.Prime 269293726253 := by
  apply lucas_primality 269293726253 (2 : ZMod 269293726253)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5563, 1), (12102001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5563, 1), (12102001, 1)] : List FactorBlock).map factorBlockValue).prod) = 269293726253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5563
      · exact prime_oneHundredFortyOneEI_12102001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 269293726253) ^ 134646863126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 269293726253) ^ 48408004 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 269293726253) ^ 22252 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_339466280899 : Nat.Prime 339466280899 := by
  apply lucas_primality 339466280899 (2 : ZMod 339466280899)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (775037171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (775037171, 1)] : List FactorBlock).map factorBlockValue).prod) = 339466280899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_73
      · exact prime_oneHundredFortyOneEI_775037171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 339466280899) ^ 169733140449 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 339466280899) ^ 113155426966 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 339466280899) ^ 4650223026 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 339466280899) ^ 438 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_412836050821 : Nat.Prime 412836050821 := by
  apply lucas_primality 412836050821 (2 : ZMod 412836050821)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (877, 1), (7845611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (877, 1), (7845611, 1)] : List FactorBlock).map factorBlockValue).prod) = 412836050821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_877
      · exact prime_oneHundredFortyOneEI_7845611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 412836050821) ^ 206418025410 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 412836050821) ^ 137612016940 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 412836050821) ^ 82567210164 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 412836050821) ^ 470736660 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 412836050821) ^ 52620 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_515760735871 : Nat.Prime 515760735871 := by
  apply lucas_primality 515760735871 (6 : ZMod 515760735871)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (233, 1), (24595171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (233, 1), (24595171, 1)] : List FactorBlock).map factorBlockValue).prod) = 515760735871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_233
      · exact prime_oneHundredFortyOneEI_24595171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 515760735871) ^ 257880367935 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 515760735871) ^ 171920245290 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 515760735871) ^ 103152147174 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 515760735871) ^ 2213565390 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 515760735871) ^ 20970 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_555197128403 : Nat.Prime 555197128403 := by
  apply lucas_primality 555197128403 (2 : ZMod 555197128403)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7027, 1), (5643509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7027, 1), (5643509, 1)] : List FactorBlock).map factorBlockValue).prod) = 555197128403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_7027
      · exact prime_oneHundredFortyOneEI_5643509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 555197128403) ^ 277598564201 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 555197128403) ^ 79313875486 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 555197128403) ^ 79009126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 555197128403) ^ 98378 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_583680336073 : Nat.Prime 583680336073 := by
  apply lucas_primality 583680336073 (15 : ZMod 583680336073)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (19, 1), (43, 1), (863, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (19, 1), (43, 1), (863, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 583680336073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_863
      · exact prime_oneHundredFortyOneEI_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 583680336073) ^ 291840168036 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (15 : ZMod 583680336073) ^ 194560112024 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (15 : ZMod 583680336073) ^ 34334137416 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (15 : ZMod 583680336073) ^ 30720017688 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (15 : ZMod 583680336073) ^ 13573961304 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (15 : ZMod 583680336073) ^ 676338744 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (15 : ZMod 583680336073) ^ 287668968 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_701291954269 : Nat.Prime 701291954269 := by
  apply lucas_primality 701291954269 (6 : ZMod 701291954269)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (6493444021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (6493444021, 1)] : List FactorBlock).map factorBlockValue).prod) = 701291954269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_6493444021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 701291954269) ^ 350645977134 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 701291954269) ^ 233763984756 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 701291954269) ^ 108 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_765116054933 : Nat.Prime 765116054933 := by
  apply lucas_primality 765116054933 (2 : ZMod 765116054933)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (131, 1), (1039, 1), (12893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (131, 1), (1039, 1), (12893, 1)] : List FactorBlock).map factorBlockValue).prod) = 765116054933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_109
      · exact prime_oneHundredFortyOneEI_131
      · exact prime_oneHundredFortyOneEI_1039
      · exact prime_oneHundredFortyOneEI_12893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 765116054933) ^ 382558027466 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 765116054933) ^ 7019413348 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 765116054933) ^ 5840580572 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 765116054933) ^ 736396588 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 765116054933) ^ 59343524 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_820641999673 : Nat.Prime 820641999673 := by
  apply lucas_primality 820641999673 (5 : ZMod 820641999673)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (11, 1), (115129349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (11, 1), (115129349, 1)] : List FactorBlock).map factorBlockValue).prod) = 820641999673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_115129349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 820641999673) ^ 410320999836 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 820641999673) ^ 273547333224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 820641999673) ^ 74603818152 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 820641999673) ^ 7128 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_821073505277 : Nat.Prime 821073505277 := by
  apply lucas_primality 821073505277 (2 : ZMod 821073505277)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3461, 1), (59308979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3461, 1), (59308979, 1)] : List FactorBlock).map factorBlockValue).prod) = 821073505277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3461
      · exact prime_oneHundredFortyOneEI_59308979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 821073505277) ^ 410536752638 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 821073505277) ^ 237235916 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 821073505277) ^ 13844 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1002676914509 : Nat.Prime 1002676914509 := by
  apply lucas_primality 1002676914509 (2 : ZMod 1002676914509)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43651, 1), (5742577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43651, 1), (5742577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1002676914509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_43651
      · exact prime_oneHundredFortyOneEI_5742577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1002676914509) ^ 501338457254 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1002676914509) ^ 22970308 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1002676914509) ^ 174604 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1163293540489 : Nat.Prime 1163293540489 := by
  apply lucas_primality 1163293540489 (13 : ZMod 1163293540489)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (811, 1), (737857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (811, 1), (737857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1163293540489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_811
      · exact prime_oneHundredFortyOneEI_737857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1163293540489) ^ 581646770244 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1163293540489) ^ 387764513496 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1163293540489) ^ 1434394008 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1163293540489) ^ 1576584 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1773769053361 : Nat.Prime 1773769053361 := by
  apply lucas_primality 1773769053361 (29 : ZMod 1773769053361)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (17, 1), (31, 1), (877, 1), (15991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (17, 1), (31, 1), (877, 1), (15991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1773769053361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_877
      · exact prime_oneHundredFortyOneEI_15991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1773769053361) ^ 886884526680 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1773769053361) ^ 591256351120 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1773769053361) ^ 354753810672 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1773769053361) ^ 104339356080 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1773769053361) ^ 57218356560 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1773769053361) ^ 2022541680 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1773769053361) ^ 110922960 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1834641690689 : Nat.Prime 1834641690689 := by
  apply lucas_primality 1834641690689 (3 : ZMod 1834641690689)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (68489, 1), (418553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (68489, 1), (418553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1834641690689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_68489
      · exact prime_oneHundredFortyOneEI_418553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1834641690689) ^ 917320845344 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1834641690689) ^ 26787392 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1834641690689) ^ 4383296 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2181449748547 : Nat.Prime 2181449748547 := by
  apply lucas_primality 2181449748547 (3 : ZMod 2181449748547)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1823, 1), (66479239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1823, 1), (66479239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2181449748547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_1823
      · exact prime_oneHundredFortyOneEI_66479239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2181449748547) ^ 1090724874273 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2181449748547) ^ 727149916182 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2181449748547) ^ 1196626302 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2181449748547) ^ 32814 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2478186304381 : Nat.Prime 2478186304381 := by
  apply lucas_primality 2478186304381 (14 : ZMod 2478186304381)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (1951, 1), (2352247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (1951, 1), (2352247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2478186304381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_1951
      · exact prime_oneHundredFortyOneEI_2352247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2478186304381) ^ 1239093152190 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 2478186304381) ^ 826062101460 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 2478186304381) ^ 495637260876 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 2478186304381) ^ 1270213380 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 2478186304381) ^ 1053540 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4421179287097 : Nat.Prime 4421179287097 := by
  apply lucas_primality 4421179287097 (7 : ZMod 4421179287097)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 2), (99094031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 2), (99094031, 1)] : List FactorBlock).map factorBlockValue).prod) = 4421179287097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_99094031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4421179287097) ^ 2210589643548 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4421179287097) ^ 1473726429032 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4421179287097) ^ 401925389736 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4421179287097) ^ 340090714392 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4421179287097) ^ 44616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4441753267351 : Nat.Prime 4441753267351 := by
  apply lucas_primality 4441753267351 (6 : ZMod 4441753267351)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (4230241207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (4230241207, 1)] : List FactorBlock).map factorBlockValue).prod) = 4441753267351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_4230241207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4441753267351) ^ 2220876633675 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4441753267351) ^ 1480584422450 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4441753267351) ^ 888350653470 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4441753267351) ^ 634536181050 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4441753267351) ^ 1050 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_5098041716153 : Nat.Prime 5098041716153 := by
  apply lucas_primality 5098041716153 (5 : ZMod 5098041716153)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (8276041747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (8276041747, 1)] : List FactorBlock).map factorBlockValue).prod) = 5098041716153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_8276041747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5098041716153) ^ 2549020858076 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5098041716153) ^ 728291673736 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5098041716153) ^ 463458337832 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5098041716153) ^ 616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_5255901536539 : Nat.Prime 5255901536539 := by
  apply lucas_primality 5255901536539 (3 : ZMod 5255901536539)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1291, 1), (678531053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1291, 1), (678531053, 1)] : List FactorBlock).map factorBlockValue).prod) = 5255901536539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_1291
      · exact prime_oneHundredFortyOneEI_678531053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5255901536539) ^ 2627950768269 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5255901536539) ^ 1751967178846 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5255901536539) ^ 4071186318 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5255901536539) ^ 7746 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_7012081213561 : Nat.Prime 7012081213561 := by
  apply lucas_primality 7012081213561 (26 : ZMod 7012081213561)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (3041, 1), (6405131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (3041, 1), (6405131, 1)] : List FactorBlock).map factorBlockValue).prod) = 7012081213561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_3041
      · exact prime_oneHundredFortyOneEI_6405131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 7012081213561) ^ 3506040606780 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (26 : ZMod 7012081213561) ^ 2337360404520 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (26 : ZMod 7012081213561) ^ 1402416242712 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (26 : ZMod 7012081213561) ^ 2305847160 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (26 : ZMod 7012081213561) ^ 1094760 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_8148857634341 : Nat.Prime 8148857634341 := by
  apply lucas_primality 8148857634341 (10 : ZMod 8148857634341)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1481, 1), (275113357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1481, 1), (275113357, 1)] : List FactorBlock).map factorBlockValue).prod) = 8148857634341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_1481
      · exact prime_oneHundredFortyOneEI_275113357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 8148857634341) ^ 4074428817170 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8148857634341) ^ 1629771526868 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8148857634341) ^ 5502267140 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8148857634341) ^ 29620 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_9887124497213 : Nat.Prime 9887124497213 := by
  apply lucas_primality 9887124497213 (2 : ZMod 9887124497213)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2609, 1), (3089, 1), (306703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2609, 1), (3089, 1), (306703, 1)] : List FactorBlock).map factorBlockValue).prod) = 9887124497213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_2609
      · exact prime_oneHundredFortyOneEI_3089
      · exact prime_oneHundredFortyOneEI_306703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9887124497213) ^ 4943562248606 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9887124497213) ^ 3789622268 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9887124497213) ^ 3200752508 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9887124497213) ^ 32236804 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_10196083432307 : Nat.Prime 10196083432307 := by
  apply lucas_primality 10196083432307 (2 : ZMod 10196083432307)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5098041716153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5098041716153, 1)] : List FactorBlock).map factorBlockValue).prod) = 10196083432307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5098041716153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10196083432307) ^ 5098041716153 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10196083432307) ^ 2 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_11475600224453 : Nat.Prime 11475600224453 := by
  apply lucas_primality 11475600224453 (2 : ZMod 11475600224453)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (13, 2), (14449, 1), (23977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (13, 2), (14449, 1), (23977, 1)] : List FactorBlock).map factorBlockValue).prod) = 11475600224453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_14449
      · exact prime_oneHundredFortyOneEI_23977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11475600224453) ^ 5737800112226 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11475600224453) ^ 1639371460636 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11475600224453) ^ 882738478804 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11475600224453) ^ 794214148 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11475600224453) ^ 478608676 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_12017485984393 : Nat.Prime 12017485984393 := by
  apply lucas_primality 12017485984393 (5 : ZMod 12017485984393)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (131, 1), (173, 1), (50101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (131, 1), (173, 1), (50101, 1)] : List FactorBlock).map factorBlockValue).prod) = 12017485984393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_131
      · exact prime_oneHundredFortyOneEI_173
      · exact prime_oneHundredFortyOneEI_50101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12017485984393) ^ 6008742992196 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 12017485984393) ^ 4005828661464 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 12017485984393) ^ 1716783712056 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 12017485984393) ^ 91736534232 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 12017485984393) ^ 69465236904 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 12017485984393) ^ 239865192 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_12187731837997 : Nat.Prime 12187731837997 := by
  apply lucas_primality 12187731837997 (2 : ZMod 12187731837997)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (13, 1), (2367469277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (13, 1), (2367469277, 1)] : List FactorBlock).map factorBlockValue).prod) = 12187731837997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_2367469277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12187731837997) ^ 6093865918998 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12187731837997) ^ 4062577279332 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12187731837997) ^ 1107975621636 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12187731837997) ^ 937517833692 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12187731837997) ^ 5148 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_13652892170881 : Nat.Prime 13652892170881 := by
  apply lucas_primality 13652892170881 (11 : ZMod 13652892170881)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (31, 1), (2521, 1), (90989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (31, 1), (2521, 1), (90989, 1)] : List FactorBlock).map factorBlockValue).prod) = 13652892170881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_2521
      · exact prime_oneHundredFortyOneEI_90989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 13652892170881) ^ 6826446085440 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 13652892170881) ^ 4550964056960 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 13652892170881) ^ 2730578434176 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 13652892170881) ^ 440415876480 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 13652892170881) ^ 5415665280 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 13652892170881) ^ 150049920 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_17491721253023 : Nat.Prime 17491721253023 := by
  apply lucas_primality 17491721253023 (5 : ZMod 17491721253023)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39367, 1), (222162233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39367, 1), (222162233, 1)] : List FactorBlock).map factorBlockValue).prod) = 17491721253023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_39367
      · exact prime_oneHundredFortyOneEI_222162233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17491721253023) ^ 8745860626511 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491721253023) ^ 444324466 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491721253023) ^ 78734 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_19613385672743 : Nat.Prime 19613385672743 := by
  apply lucas_primality 19613385672743 (5 : ZMod 19613385672743)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (976109, 1), (10046719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (976109, 1), (10046719, 1)] : List FactorBlock).map factorBlockValue).prod) = 19613385672743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_976109
      · exact prime_oneHundredFortyOneEI_10046719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19613385672743) ^ 9806692836371 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19613385672743) ^ 20093438 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19613385672743) ^ 1952218 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_19684487723917 : Nat.Prime 19684487723917 := by
  apply lucas_primality 19684487723917 (5 : ZMod 19684487723917)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (14747, 1), (111234419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (14747, 1), (111234419, 1)] : List FactorBlock).map factorBlockValue).prod) = 19684487723917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_14747
      · exact prime_oneHundredFortyOneEI_111234419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19684487723917) ^ 9842243861958 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19684487723917) ^ 6561495907972 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19684487723917) ^ 1334813028 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19684487723917) ^ 176964 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_22573950515551 : Nat.Prime 22573950515551 := by
  apply lucas_primality 22573950515551 (3 : ZMod 22573950515551)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (61, 1), (101, 1), (1163177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (61, 1), (101, 1), (1163177, 1)] : List FactorBlock).map factorBlockValue).prod) = 22573950515551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_61
      · exact prime_oneHundredFortyOneEI_101
      · exact prime_oneHundredFortyOneEI_1163177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22573950515551) ^ 11286975257775 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22573950515551) ^ 7524650171850 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22573950515551) ^ 4514790103110 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22573950515551) ^ 3224850073650 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22573950515551) ^ 370064762550 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22573950515551) ^ 223504460550 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22573950515551) ^ 19407150 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_24120413962693 : Nat.Prime 24120413962693 := by
  apply lucas_primality 24120413962693 (2 : ZMod 24120413962693)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2141, 1), (938829751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2141, 1), (938829751, 1)] : List FactorBlock).map factorBlockValue).prod) = 24120413962693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_2141
      · exact prime_oneHundredFortyOneEI_938829751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24120413962693) ^ 12060206981346 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24120413962693) ^ 8040137987564 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24120413962693) ^ 11265957012 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24120413962693) ^ 25692 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_28314074367937 : Nat.Prime 28314074367937 := by
  apply lucas_primality 28314074367937 (10 : ZMod 28314074367937)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (7, 1), (1013, 1), (6932221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (7, 1), (1013, 1), (6932221, 1)] : List FactorBlock).map factorBlockValue).prod) = 28314074367937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_1013
      · exact prime_oneHundredFortyOneEI_6932221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 28314074367937) ^ 14157037183968 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 28314074367937) ^ 9438024789312 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 28314074367937) ^ 4044867766848 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 28314074367937) ^ 27950715072 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 28314074367937) ^ 4084416 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_37960126682077 : Nat.Prime 37960126682077 := by
  apply lucas_primality 37960126682077 (5 : ZMod 37960126682077)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (683, 1), (1543847677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (683, 1), (1543847677, 1)] : List FactorBlock).map factorBlockValue).prod) = 37960126682077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_683
      · exact prime_oneHundredFortyOneEI_1543847677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37960126682077) ^ 18980063341038 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37960126682077) ^ 12653375560692 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37960126682077) ^ 55578516372 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37960126682077) ^ 24588 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_41184729066599 : Nat.Prime 41184729066599 := by
  apply lucas_primality 41184729066599 (17 : ZMod 41184729066599)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (173, 1), (315732119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (173, 1), (315732119, 1)] : List FactorBlock).map factorBlockValue).prod) = 41184729066599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_29
      · exact prime_oneHundredFortyOneEI_173
      · exact prime_oneHundredFortyOneEI_315732119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 41184729066599) ^ 20592364533299 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 41184729066599) ^ 3168056082046 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 41184729066599) ^ 1420163071262 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 41184729066599) ^ 238062017726 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (17 : ZMod 41184729066599) ^ 130442 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_41357384018707 : Nat.Prime 41357384018707 := by
  apply lucas_primality 41357384018707 (11 : ZMod 41357384018707)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (43, 1), (61, 1), (97, 2), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (43, 1), (61, 1), (97, 2), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) = 41357384018707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_61
      · exact prime_oneHundredFortyOneEI_97
      · exact prime_oneHundredFortyOneEI_2347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 41357384018707) ^ 20678692009353 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 13785794672902 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 5908197716958 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 2432787295218 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 961799628342 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 677989901946 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 426364783698 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 41357384018707) ^ 17621382198 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_41902118173043 : Nat.Prime 41902118173043 := by
  apply lucas_primality 41902118173043 (2 : ZMod 41902118173043)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (99149, 1), (470621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (99149, 1), (470621, 1)] : List FactorBlock).map factorBlockValue).prod) = 41902118173043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_449
      · exact prime_oneHundredFortyOneEI_99149
      · exact prime_oneHundredFortyOneEI_470621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41902118173043) ^ 20951059086521 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41902118173043) ^ 93323203058 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41902118173043) ^ 422617658 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41902118173043) ^ 89035802 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_44097109317407 : Nat.Prime 44097109317407 := by
  apply lucas_primality 44097109317407 (5 : ZMod 44097109317407)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3361, 1), (6560117423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3361, 1), (6560117423, 1)] : List FactorBlock).map factorBlockValue).prod) = 44097109317407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3361
      · exact prime_oneHundredFortyOneEI_6560117423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 44097109317407) ^ 22048554658703 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 44097109317407) ^ 13120234846 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 44097109317407) ^ 6722 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_55741050679849 : Nat.Prime 55741050679849 := by
  apply lucas_primality 55741050679849 (7 : ZMod 55741050679849)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (829, 1), (2801620963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (829, 1), (2801620963, 1)] : List FactorBlock).map factorBlockValue).prod) = 55741050679849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_829
      · exact prime_oneHundredFortyOneEI_2801620963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 55741050679849) ^ 27870525339924 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 55741050679849) ^ 18580350226616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 55741050679849) ^ 67238903112 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 55741050679849) ^ 19896 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_57206030476307 : Nat.Prime 57206030476307 := by
  apply lucas_primality 57206030476307 (2 : ZMod 57206030476307)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1313057, 1), (21783529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1313057, 1), (21783529, 1)] : List FactorBlock).map factorBlockValue).prod) = 57206030476307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1313057
      · exact prime_oneHundredFortyOneEI_21783529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57206030476307) ^ 28603015238153 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57206030476307) ^ 43567058 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57206030476307) ^ 2626114 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_104558102728259 : Nat.Prime 104558102728259 := by
  apply lucas_primality 104558102728259 (2 : ZMod 104558102728259)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (1021, 1), (130955939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (1021, 1), (130955939, 1)] : List FactorBlock).map factorBlockValue).prod) = 104558102728259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_1021
      · exact prime_oneHundredFortyOneEI_130955939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104558102728259) ^ 52279051364129 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104558102728259) ^ 6150476631074 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104558102728259) ^ 4546004466446 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104558102728259) ^ 102407544298 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104558102728259) ^ 798422 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_125279698949149 : Nat.Prime 125279698949149 := by
  apply lucas_primality 125279698949149 (2 : ZMod 125279698949149)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149, 1), (246613, 1), (284117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149, 1), (246613, 1), (284117, 1)] : List FactorBlock).map factorBlockValue).prod) = 125279698949149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_149
      · exact prime_oneHundredFortyOneEI_246613
      · exact prime_oneHundredFortyOneEI_284117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125279698949149) ^ 62639849474574 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125279698949149) ^ 41759899649716 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125279698949149) ^ 840803348652 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125279698949149) ^ 508001196 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125279698949149) ^ 440944044 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_153238383473801 : Nat.Prime 153238383473801 := by
  apply lucas_primality 153238383473801 (3 : ZMod 153238383473801)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (43, 1), (9767, 1), (1824349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (43, 1), (9767, 1), (1824349, 1)] : List FactorBlock).map factorBlockValue).prod) = 153238383473801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_9767
      · exact prime_oneHundredFortyOneEI_1824349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 153238383473801) ^ 76619191736900 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 153238383473801) ^ 30647676694760 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 153238383473801) ^ 3563683336600 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 153238383473801) ^ 15689401400 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 153238383473801) ^ 83996200 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_263538475897247 : Nat.Prime 263538475897247 := by
  apply lucas_primality 263538475897247 (5 : ZMod 263538475897247)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2621, 1), (4570401233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2621, 1), (4570401233, 1)] : List FactorBlock).map factorBlockValue).prod) = 263538475897247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_2621
      · exact prime_oneHundredFortyOneEI_4570401233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 263538475897247) ^ 131769237948623 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 263538475897247) ^ 23958043263386 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 263538475897247) ^ 100548827126 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 263538475897247) ^ 57662 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_348410511956347 : Nat.Prime 348410511956347 := by
  apply lucas_primality 348410511956347 (2 : ZMod 348410511956347)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (12553, 1), (94405303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (12553, 1), (94405303, 1)] : List FactorBlock).map factorBlockValue).prod) = 348410511956347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_12553
      · exact prime_oneHundredFortyOneEI_94405303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 348410511956347) ^ 174205255978173 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 348410511956347) ^ 116136837318782 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 348410511956347) ^ 49772930279478 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 348410511956347) ^ 27755159082 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 348410511956347) ^ 3690582 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_353829892068589 : Nat.Prime 353829892068589 := by
  apply lucas_primality 353829892068589 (6 : ZMod 353829892068589)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (89123, 1), (25449551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (89123, 1), (25449551, 1)] : List FactorBlock).map factorBlockValue).prod) = 353829892068589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_89123
      · exact prime_oneHundredFortyOneEI_25449551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 353829892068589) ^ 176914946034294 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 353829892068589) ^ 117943297356196 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 353829892068589) ^ 27217684005276 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 353829892068589) ^ 3970129956 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 353829892068589) ^ 13903188 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_364842449723707 : Nat.Prime 364842449723707 := by
  apply lucas_primality 364842449723707 (3 : ZMod 364842449723707)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (599, 1), (23431, 1), (4332479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (599, 1), (23431, 1), (4332479, 1)] : List FactorBlock).map factorBlockValue).prod) = 364842449723707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_599
      · exact prime_oneHundredFortyOneEI_23431
      · exact prime_oneHundredFortyOneEI_4332479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 364842449723707) ^ 182421224861853 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 364842449723707) ^ 121614149907902 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 364842449723707) ^ 609085892694 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 364842449723707) ^ 15570929526 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 364842449723707) ^ 84211014 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_413174124217579 : Nat.Prime 413174124217579 := by
  apply lucas_primality 413174124217579 (2 : ZMod 413174124217579)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (388727, 1), (7702103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (388727, 1), (7702103, 1)] : List FactorBlock).map factorBlockValue).prod) = 413174124217579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_388727
      · exact prime_oneHundredFortyOneEI_7702103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 413174124217579) ^ 206587062108789 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 413174124217579) ^ 137724708072526 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 413174124217579) ^ 17964092357286 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 413174124217579) ^ 1062890214 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 413174124217579) ^ 53644326 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_455402582352227 : Nat.Prime 455402582352227 := by
  apply lucas_primality 455402582352227 (2 : ZMod 455402582352227)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (174721, 1), (6823183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (174721, 1), (6823183, 1)] : List FactorBlock).map factorBlockValue).prod) = 455402582352227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_191
      · exact prime_oneHundredFortyOneEI_174721
      · exact prime_oneHundredFortyOneEI_6823183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 455402582352227) ^ 227701291176113 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 455402582352227) ^ 2384306713886 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 455402582352227) ^ 2606455906 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 455402582352227) ^ 66743422 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_466514098911691 : Nat.Prime 466514098911691 := by
  apply lucas_primality 466514098911691 (3 : ZMod 466514098911691)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (103, 1), (150975436541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (103, 1), (150975436541, 1)] : List FactorBlock).map factorBlockValue).prod) = 466514098911691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_103
      · exact prime_oneHundredFortyOneEI_150975436541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 466514098911691) ^ 233257049455845 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 466514098911691) ^ 155504699637230 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 466514098911691) ^ 93302819782338 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 466514098911691) ^ 4529263096230 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 466514098911691) ^ 3090 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_467561026671877 : Nat.Prime 467561026671877 := by
  apply lucas_primality 467561026671877 (2 : ZMod 467561026671877)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (3463, 1), (220614671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (3463, 1), (220614671, 1)] : List FactorBlock).map factorBlockValue).prod) = 467561026671877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_3463
      · exact prime_oneHundredFortyOneEI_220614671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 467561026671877) ^ 233780513335938 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 467561026671877) ^ 155853675557292 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 467561026671877) ^ 27503589804228 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 467561026671877) ^ 135016178652 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 467561026671877) ^ 2119356 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_579232031445481 : Nat.Prime 579232031445481 := by
  apply lucas_primality 579232031445481 (13 : ZMod 579232031445481)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (4639, 1), (148644523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (4639, 1), (148644523, 1)] : List FactorBlock).map factorBlockValue).prod) = 579232031445481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_4639
      · exact prime_oneHundredFortyOneEI_148644523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 579232031445481) ^ 289616015722740 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 579232031445481) ^ 193077343815160 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 579232031445481) ^ 115846406289096 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 579232031445481) ^ 82747433063640 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 579232031445481) ^ 124861399320 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 579232031445481) ^ 3896760 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_620296439088919 : Nat.Prime 620296439088919 := by
  apply lucas_primality 620296439088919 (3 : ZMod 620296439088919)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (127, 1), (45893, 1), (156971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (127, 1), (45893, 1), (156971, 1)] : List FactorBlock).map factorBlockValue).prod) = 620296439088919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_113
      · exact prime_oneHundredFortyOneEI_127
      · exact prime_oneHundredFortyOneEI_45893
      · exact prime_oneHundredFortyOneEI_156971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 620296439088919) ^ 310148219544459 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 620296439088919) ^ 206765479696306 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 620296439088919) ^ 5489349018486 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 620296439088919) ^ 4884223929834 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 620296439088919) ^ 13516144926 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 620296439088919) ^ 3951662658 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1227235137601537 : Nat.Prime 1227235137601537 := by
  apply lucas_primality 1227235137601537 (10 : ZMod 1227235137601537)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 14), (3, 2), (7, 1), (1188960133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 14), (3, 2), (7, 1), (1188960133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1227235137601537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_1188960133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1227235137601537) ^ 613617568800768 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 1227235137601537) ^ 409078379200512 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 1227235137601537) ^ 175319305371648 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 1227235137601537) ^ 1032192 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1291744874386529 : Nat.Prime 1291744874386529 := by
  apply lucas_primality 1291744874386529 (3 : ZMod 1291744874386529)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (983, 1), (1979, 1), (20750447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (983, 1), (1979, 1), (20750447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291744874386529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_983
      · exact prime_oneHundredFortyOneEI_1979
      · exact prime_oneHundredFortyOneEI_20750447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1291744874386529) ^ 645872437193264 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1291744874386529) ^ 1314084307616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1291744874386529) ^ 652726060832 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1291744874386529) ^ 62251424 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2398728273085007 : Nat.Prime 2398728273085007 := by
  apply lucas_primality 2398728273085007 (5 : ZMod 2398728273085007)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (41357384018707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (41357384018707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2398728273085007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_29
      · exact prime_oneHundredFortyOneEI_41357384018707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2398728273085007) ^ 1199364136542503 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2398728273085007) ^ 82714768037414 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2398728273085007) ^ 58 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2542326376834141 : Nat.Prime 2542326376834141 := by
  apply lucas_primality 2542326376834141 (2 : ZMod 2542326376834141)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (37, 2), (59, 1), (233, 1), (173191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (37, 2), (59, 1), (233, 1), (173191, 1)] : List FactorBlock).map factorBlockValue).prod) = 2542326376834141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_59
      · exact prime_oneHundredFortyOneEI_233
      · exact prime_oneHundredFortyOneEI_173191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2542326376834141) ^ 1271163188417070 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 847442125611380 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 508465275366828 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 195563567448780 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 68711523698220 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 43090277573460 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 10911272003580 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2542326376834141) ^ 14679321540 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6457424838274547 : Nat.Prime 6457424838274547 := by
  apply lucas_primality 6457424838274547 (2 : ZMod 6457424838274547)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4139, 1), (290359, 1), (2686573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4139, 1), (290359, 1), (2686573, 1)] : List FactorBlock).map factorBlockValue).prod) = 6457424838274547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_4139
      · exact prime_oneHundredFortyOneEI_290359
      · exact prime_oneHundredFortyOneEI_2686573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6457424838274547) ^ 3228712419137273 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6457424838274547) ^ 1560141299414 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6457424838274547) ^ 22239451294 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6457424838274547) ^ 2403591802 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6530960457523673 : Nat.Prime 6530960457523673 := by
  apply lucas_primality 6530960457523673 (3 : ZMod 6530960457523673)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (2671, 1), (30493, 1), (589609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (2671, 1), (30493, 1), (589609, 1)] : List FactorBlock).map factorBlockValue).prod) = 6530960457523673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_2671
      · exact prime_oneHundredFortyOneEI_30493
      · exact prime_oneHundredFortyOneEI_589609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6530960457523673) ^ 3265480228761836 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6530960457523673) ^ 384174144560216 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6530960457523673) ^ 2445136824232 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6530960457523673) ^ 214179006904 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6530960457523673) ^ 11076765208 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_9188531244560477 : Nat.Prime 9188531244560477 := by
  apply lucas_primality 9188531244560477 (2 : ZMod 9188531244560477)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (79, 1), (1002676914509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (79, 1), (1002676914509, 1)] : List FactorBlock).map factorBlockValue).prod) = 9188531244560477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_29
      · exact prime_oneHundredFortyOneEI_79
      · exact prime_oneHundredFortyOneEI_1002676914509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9188531244560477) ^ 4594265622280238 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9188531244560477) ^ 316845904984844 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9188531244560477) ^ 116310522083044 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9188531244560477) ^ 9164 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_16649295759277771 : Nat.Prime 16649295759277771 := by
  apply lucas_primality 16649295759277771 (2 : ZMod 16649295759277771)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (12379, 1), (44832096721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (12379, 1), (44832096721, 1)] : List FactorBlock).map factorBlockValue).prod) = 16649295759277771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_12379
      · exact prime_oneHundredFortyOneEI_44832096721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16649295759277771) ^ 8324647879638885 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16649295759277771) ^ 5549765253092590 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16649295759277771) ^ 3329859151855554 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16649295759277771) ^ 1344962901630 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16649295759277771) ^ 371370 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_22331124746015159 : Nat.Prime 22331124746015159 := by
  apply lucas_primality 22331124746015159 (7 : ZMod 22331124746015159)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (153487, 1), (72745980917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (153487, 1), (72745980917, 1)] : List FactorBlock).map factorBlockValue).prod) = 22331124746015159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_153487
      · exact prime_oneHundredFortyOneEI_72745980917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 22331124746015159) ^ 11165562373007579 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 22331124746015159) ^ 145491961834 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 22331124746015159) ^ 306974 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_23083078670892329 : Nat.Prime 23083078670892329 := by
  apply lucas_primality 23083078670892329 (3 : ZMod 23083078670892329)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (83, 1), (103, 1), (479, 1), (64056061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (83, 1), (103, 1), (479, 1), (64056061, 1)] : List FactorBlock).map factorBlockValue).prod) = 23083078670892329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_83
      · exact prime_oneHundredFortyOneEI_103
      · exact prime_oneHundredFortyOneEI_479
      · exact prime_oneHundredFortyOneEI_64056061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23083078670892329) ^ 11541539335446164 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23083078670892329) ^ 2098461697353848 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23083078670892329) ^ 278109381577016 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23083078670892329) ^ 224107559911576 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23083078670892329) ^ 48190143363032 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23083078670892329) ^ 360357448 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_33633393575737661 : Nat.Prime 33633393575737661 := by
  apply lucas_primality 33633393575737661 (2 : ZMod 33633393575737661)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (349, 1), (1297, 1), (6397, 1), (580763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (349, 1), (1297, 1), (6397, 1), (580763, 1)] : List FactorBlock).map factorBlockValue).prod) = 33633393575737661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_349
      · exact prime_oneHundredFortyOneEI_1297
      · exact prime_oneHundredFortyOneEI_6397
      · exact prime_oneHundredFortyOneEI_580763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33633393575737661) ^ 16816696787868830 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633393575737661) ^ 6726678715147532 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633393575737661) ^ 96370755231340 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633393575737661) ^ 25931683558780 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633393575737661) ^ 5257682284780 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633393575737661) ^ 57912424820 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_44417532673510001 : Nat.Prime 44417532673510001 := by
  apply lucas_primality 44417532673510001 (3 : ZMod 44417532673510001)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 4), (4441753267351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 4), (4441753267351, 1)] : List FactorBlock).map factorBlockValue).prod) = 44417532673510001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_4441753267351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44417532673510001) ^ 22208766336755000 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 44417532673510001) ^ 8883506534702000 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 44417532673510001) ^ 10000 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_58069038084252059 : Nat.Prime 58069038084252059 := by
  apply lucas_primality 58069038084252059 (2 : ZMod 58069038084252059)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1489, 1), (1293757, 1), (15071873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1489, 1), (1293757, 1), (15071873, 1)] : List FactorBlock).map factorBlockValue).prod) = 58069038084252059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1489
      · exact prime_oneHundredFortyOneEI_1293757
      · exact prime_oneHundredFortyOneEI_15071873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58069038084252059) ^ 29034519042126029 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58069038084252059) ^ 38998682393722 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58069038084252059) ^ 44884037794 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58069038084252059) ^ 3852808346 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_59324766587859613 : Nat.Prime 59324766587859613 := by
  apply lucas_primality 59324766587859613 (2 : ZMod 59324766587859613)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (3907, 1), (10633210697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (3907, 1), (10633210697, 1)] : List FactorBlock).map factorBlockValue).prod) = 59324766587859613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_3907
      · exact prime_oneHundredFortyOneEI_10633210697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59324766587859613) ^ 29662383293929806 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59324766587859613) ^ 19774922195953204 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59324766587859613) ^ 8474966655408516 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59324766587859613) ^ 3489692152227036 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59324766587859613) ^ 15184224875316 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59324766587859613) ^ 5579196 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_59490096184097429 : Nat.Prime 59490096184097429 := by
  apply lucas_primality 59490096184097429 (2 : ZMod 59490096184097429)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (184843, 1), (80460304399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (184843, 1), (80460304399, 1)] : List FactorBlock).map factorBlockValue).prod) = 59490096184097429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_184843
      · exact prime_oneHundredFortyOneEI_80460304399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59490096184097429) ^ 29745048092048714 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59490096184097429) ^ 321841217596 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 59490096184097429) ^ 739372 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_101785534841994791 : Nat.Prime 101785534841994791 := by
  apply lucas_primality 101785534841994791 (7 : ZMod 101785534841994791)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113963, 1), (89314544933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113963, 1), (89314544933, 1)] : List FactorBlock).map factorBlockValue).prod) = 101785534841994791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_113963
      · exact prime_oneHundredFortyOneEI_89314544933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 101785534841994791) ^ 50892767420997395 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 101785534841994791) ^ 20357106968398958 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 101785534841994791) ^ 893145449330 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 101785534841994791) ^ 1139630 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_108499555218664009 : Nat.Prime 108499555218664009 := by
  apply lucas_primality 108499555218664009 (19 : ZMod 108499555218664009)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 4), (31, 1), (67, 1), (71, 1), (1418689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 4), (31, 1), (67, 1), (71, 1), (1418689, 1)] : List FactorBlock).map factorBlockValue).prod) = 108499555218664009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_67
      · exact prime_oneHundredFortyOneEI_71
      · exact prime_oneHundredFortyOneEI_1418689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 108499555218664009) ^ 54249777609332004 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 108499555218664009) ^ 36166518406221336 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 108499555218664009) ^ 15499936459809144 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 108499555218664009) ^ 3499985652214968 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 108499555218664009) ^ 1619396346547224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 108499555218664009) ^ 1528162749558648 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 108499555218664009) ^ 76478745672 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_136038443026145449 : Nat.Prime 136038443026145449 := by
  apply lucas_primality 136038443026145449 (7 : ZMod 136038443026145449)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 2), (19613385672743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 2), (19613385672743, 1)] : List FactorBlock).map factorBlockValue).prod) = 136038443026145449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_19613385672743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 136038443026145449) ^ 68019221513072724 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 136038443026145449) ^ 45346147675381816 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 136038443026145449) ^ 8002261354479144 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 136038443026145449) ^ 6936 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_186965522851394873 : Nat.Prime 186965522851394873 := by
  apply lucas_primality 186965522851394873 (3 : ZMod 186965522851394873)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (181, 1), (1103561, 1), (9000223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (181, 1), (1103561, 1), (9000223, 1)] : List FactorBlock).map factorBlockValue).prod) = 186965522851394873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_181
      · exact prime_oneHundredFortyOneEI_1103561
      · exact prime_oneHundredFortyOneEI_9000223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 186965522851394873) ^ 93482761425697436 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 186965522851394873) ^ 14381963296261144 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 186965522851394873) ^ 1032958689786712 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 186965522851394873) ^ 169420197752 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 186965522851394873) ^ 20773432264 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_357980333438710027 : Nat.Prime 357980333438710027 := by
  apply lucas_primality 357980333438710027 (3 : ZMod 357980333438710027)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (41, 1), (44097109317407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (41, 1), (44097109317407, 1)] : List FactorBlock).map factorBlockValue).prod) = 357980333438710027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_41
      · exact prime_oneHundredFortyOneEI_44097109317407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 357980333438710027) ^ 178990166719355013 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 357980333438710027) ^ 119326777812903342 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 357980333438710027) ^ 32543666676246366 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 357980333438710027) ^ 8731227644846586 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 357980333438710027) ^ 8118 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_361867362954505987 : Nat.Prime 361867362954505987 := by
  apply lucas_primality 361867362954505987 (2 : ZMod 361867362954505987)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (23981, 1), (62141, 1), (400711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (23981, 1), (62141, 1), (400711, 1)] : List FactorBlock).map factorBlockValue).prod) = 361867362954505987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_101
      · exact prime_oneHundredFortyOneEI_23981
      · exact prime_oneHundredFortyOneEI_62141
      · exact prime_oneHundredFortyOneEI_400711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 361867362954505987) ^ 180933681477252993 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 361867362954505987) ^ 120622454318168662 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 361867362954505987) ^ 3582845177767386 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 361867362954505987) ^ 15089752844106 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 361867362954505987) ^ 5823326997546 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 361867362954505987) ^ 903063212526 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_384361324730467631 : Nat.Prime 384361324730467631 := by
  apply lucas_primality 384361324730467631 (14 : ZMod 384361324730467631)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (353, 1), (401, 1), (18313, 1), (162937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (353, 1), (401, 1), (18313, 1), (162937, 1)] : List FactorBlock).map factorBlockValue).prod) = 384361324730467631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_353
      · exact prime_oneHundredFortyOneEI_401
      · exact prime_oneHundredFortyOneEI_18313
      · exact prime_oneHundredFortyOneEI_162937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 384361324730467631) ^ 192180662365233815 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 76872264946093526 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 54908760675781090 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 29566255748497510 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 1088842279689710 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 958507044215630 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 20988441256510 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 384361324730467631) ^ 2358956680990 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_492268347593418997 : Nat.Prime 492268347593418997 := by
  apply lucas_primality 492268347593418997 (2 : ZMod 492268347593418997)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1685779, 1), (8111455159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1685779, 1), (8111455159, 1)] : List FactorBlock).map factorBlockValue).prod) = 492268347593418997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_1685779
      · exact prime_oneHundredFortyOneEI_8111455159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 492268347593418997) ^ 246134173796709498 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492268347593418997) ^ 164089449197806332 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492268347593418997) ^ 292012385724 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492268347593418997) ^ 60688044 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_546539261304368309 : Nat.Prime 546539261304368309 := by
  apply lucas_primality 546539261304368309 (2 : ZMod 546539261304368309)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (43, 1), (197, 1), (701291954269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (43, 1), (197, 1), (701291954269, 1)] : List FactorBlock).map factorBlockValue).prod) = 546539261304368309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_197
      · exact prime_oneHundredFortyOneEI_701291954269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 546539261304368309) ^ 273269630652184154 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 546539261304368309) ^ 23762576578450796 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 546539261304368309) ^ 12710215379171356 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 546539261304368309) ^ 2774310971088164 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 546539261304368309) ^ 779332 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_619025303626585643 : Nat.Prime 619025303626585643 := by
  apply lucas_primality 619025303626585643 (2 : ZMod 619025303626585643)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9861349, 1), (31386441329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9861349, 1), (31386441329, 1)] : List FactorBlock).map factorBlockValue).prod) = 619025303626585643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_9861349
      · exact prime_oneHundredFortyOneEI_31386441329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 619025303626585643) ^ 309512651813292821 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 619025303626585643) ^ 62772882658 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 619025303626585643) ^ 19722698 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_825120905325324661 : Nat.Prime 825120905325324661 := by
  apply lucas_primality 825120905325324661 (10 : ZMod 825120905325324661)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (13, 1), (59, 1), (463, 1), (27361, 1), (157259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (13, 1), (59, 1), (463, 1), (27361, 1), (157259, 1)] : List FactorBlock).map factorBlockValue).prod) = 825120905325324661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_59
      · exact prime_oneHundredFortyOneEI_463
      · exact prime_oneHundredFortyOneEI_27361
      · exact prime_oneHundredFortyOneEI_157259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 825120905325324661) ^ 412560452662662330 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 275040301775108220 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 165024181065064932 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 63470838871178820 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 13985100090259740 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 1782118586015820 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 30156825603060 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (10 : ZMod 825120905325324661) ^ 5246891467740 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_845780988571685051 : Nat.Prime 845780988571685051 := by
  apply lucas_primality 845780988571685051 (6 : ZMod 845780988571685051)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (1223, 1), (82241, 1), (8851553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (1223, 1), (82241, 1), (8851553, 1)] : List FactorBlock).map factorBlockValue).prod) = 845780988571685051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_1223
      · exact prime_oneHundredFortyOneEI_82241
      · exact prime_oneHundredFortyOneEI_8851553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 845780988571685051) ^ 422890494285842525 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 845780988571685051) ^ 169156197714337010 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 845780988571685051) ^ 44514788872193950 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 845780988571685051) ^ 691562541759350 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 845780988571685051) ^ 10284176853050 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 845780988571685051) ^ 95551705850 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1047301903215659579 : Nat.Prime 1047301903215659579 := by
  apply lucas_primality 1047301903215659579 (2 : ZMod 1047301903215659579)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1987, 1), (263538475897247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1987, 1), (263538475897247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047301903215659579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1987
      · exact prime_oneHundredFortyOneEI_263538475897247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1047301903215659579) ^ 523650951607829789 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1047301903215659579) ^ 527076951794494 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1047301903215659579) ^ 3974 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1139688826856462357 : Nat.Prime 1139688826856462357 := by
  apply lucas_primality 1139688826856462357 (2 : ZMod 1139688826856462357)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (509, 1), (13652892170881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (509, 1), (13652892170881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139688826856462357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_41
      · exact prime_oneHundredFortyOneEI_509
      · exact prime_oneHundredFortyOneEI_13652892170881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1139688826856462357) ^ 569844413428231178 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139688826856462357) ^ 27797288459913716 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139688826856462357) ^ 2239074316024484 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139688826856462357) ^ 83476 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1672919558697323927 : Nat.Prime 1672919558697323927 := by
  apply lucas_primality 1672919558697323927 (5 : ZMod 1672919558697323927)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (163, 1), (466514098911691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (163, 1), (466514098911691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1672919558697323927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_163
      · exact prime_oneHundredFortyOneEI_466514098911691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1672919558697323927) ^ 836459779348661963 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1672919558697323927) ^ 152083596245211266 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1672919558697323927) ^ 10263310176057202 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1672919558697323927) ^ 3586 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2709690740803043707 : Nat.Prime 2709690740803043707 := by
  apply lucas_primality 2709690740803043707 (5 : ZMod 2709690740803043707)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (44293, 1), (10196083432307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (44293, 1), (10196083432307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2709690740803043707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_44293
      · exact prime_oneHundredFortyOneEI_10196083432307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2709690740803043707) ^ 1354845370401521853 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709690740803043707) ^ 903230246934347902 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709690740803043707) ^ 61176500593842 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709690740803043707) ^ 265758 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4228482415642422103 : Nat.Prime 4228482415642422103 := by
  apply lucas_primality 4228482415642422103 (3 : ZMod 4228482415642422103)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (41, 1), (7974227, 1), (21773369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (41, 1), (7974227, 1), (21773369, 1)] : List FactorBlock).map factorBlockValue).prod) = 4228482415642422103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_41
      · exact prime_oneHundredFortyOneEI_7974227
      · exact prime_oneHundredFortyOneEI_21773369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4228482415642422103) ^ 2114241207821211051 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4228482415642422103) ^ 1409494138547474034 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4228482415642422103) ^ 384407492331129282 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4228482415642422103) ^ 103133717454693222 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4228482415642422103) ^ 530268628626 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4228482415642422103) ^ 194204324358 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4804371487349365781 : Nat.Prime 4804371487349365781 := by
  apply lucas_primality 4804371487349365781 (3 : ZMod 4804371487349365781)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (84047869, 1), (2858116181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (84047869, 1), (2858116181, 1)] : List FactorBlock).map factorBlockValue).prod) = 4804371487349365781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_84047869
      · exact prime_oneHundredFortyOneEI_2858116181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4804371487349365781) ^ 2402185743674682890 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4804371487349365781) ^ 960874297469873156 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4804371487349365781) ^ 57162323620 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4804371487349365781) ^ 1680957380 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_5695177592434522849 : Nat.Prime 5695177592434522849 := by
  apply lucas_primality 5695177592434522849 (7 : ZMod 5695177592434522849)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (59324766587859613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (59324766587859613, 1)] : List FactorBlock).map factorBlockValue).prod) = 5695177592434522849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_59324766587859613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5695177592434522849) ^ 2847588796217261424 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 5695177592434522849) ^ 1898392530811507616 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 5695177592434522849) ^ 96 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6379402820491074749 : Nat.Prime 6379402820491074749 := by
  apply lucas_primality 6379402820491074749 (2 : ZMod 6379402820491074749)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (3150877, 1), (2000635927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (3150877, 1), (2000635927, 1)] : List FactorBlock).map factorBlockValue).prod) = 6379402820491074749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_3150877
      · exact prime_oneHundredFortyOneEI_2000635927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6379402820491074749) ^ 3189701410245537374 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6379402820491074749) ^ 579945710953734068 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6379402820491074749) ^ 277365340021351076 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6379402820491074749) ^ 2024643558124 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6379402820491074749) ^ 3188687524 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6970704361585030343 : Nat.Prime 6970704361585030343 := by
  apply lucas_primality 6970704361585030343 (5 : ZMod 6970704361585030343)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1453, 1), (2398728273085007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1453, 1), (2398728273085007, 1)] : List FactorBlock).map factorBlockValue).prod) = 6970704361585030343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1453
      · exact prime_oneHundredFortyOneEI_2398728273085007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6970704361585030343) ^ 3485352180792515171 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6970704361585030343) ^ 4797456546170014 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6970704361585030343) ^ 2906 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_23960235660386237503 : Nat.Prime 23960235660386237503 := by
  apply lucas_primality 23960235660386237503 (6 : ZMod 23960235660386237503)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (23083078670892329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (23083078670892329, 1)] : List FactorBlock).map factorBlockValue).prod) = 23960235660386237503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_173
      · exact prime_oneHundredFortyOneEI_23083078670892329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 23960235660386237503) ^ 11980117830193118751 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 23960235660386237503) ^ 7986745220128745834 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 23960235660386237503) ^ 138498472025353974 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 23960235660386237503) ^ 1038 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_28826228924096194687 : Nat.Prime 28826228924096194687 := by
  apply lucas_primality 28826228924096194687 (3 : ZMod 28826228924096194687)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4804371487349365781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4804371487349365781, 1)] : List FactorBlock).map factorBlockValue).prod) = 28826228924096194687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_4804371487349365781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28826228924096194687) ^ 14413114462048097343 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28826228924096194687) ^ 9608742974698731562 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28826228924096194687) ^ 6 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_30458686443872026553 : Nat.Prime 30458686443872026553 := by
  apply lucas_primality 30458686443872026553 (3 : ZMod 30458686443872026553)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (205870607, 1), (18493829017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (205870607, 1), (18493829017, 1)] : List FactorBlock).map factorBlockValue).prod) = 30458686443872026553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_205870607
      · exact prime_oneHundredFortyOneEI_18493829017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30458686443872026553) ^ 15229343221936013276 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30458686443872026553) ^ 147950632136 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30458686443872026553) ^ 1646964856 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_38347952137662136537 : Nat.Prime 38347952137662136537 := by
  apply lucas_primality 38347952137662136537 (5 : ZMod 38347952137662136537)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (7, 1), (19, 1), (2129, 1), (208996911551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (7, 1), (19, 1), (2129, 1), (208996911551, 1)] : List FactorBlock).map factorBlockValue).prod) = 38347952137662136537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_2129
      · exact prime_oneHundredFortyOneEI_208996911551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38347952137662136537) ^ 19173976068831068268 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 38347952137662136537) ^ 12782650712554045512 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 38347952137662136537) ^ 5478278876808876648 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 38347952137662136537) ^ 2018313270403270344 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 38347952137662136537) ^ 18012189825111384 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 38347952137662136537) ^ 183485736 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_51035222563928597993 : Nat.Prime 51035222563928597993 := by
  apply lucas_primality 51035222563928597993 (3 : ZMod 51035222563928597993)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6379402820491074749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6379402820491074749, 1)] : List FactorBlock).map factorBlockValue).prod) = 51035222563928597993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_6379402820491074749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 51035222563928597993) ^ 25517611281964298996 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 51035222563928597993) ^ 8 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_74624307270857125129 : Nat.Prime 74624307270857125129 := by
  apply lucas_primality 74624307270857125129 (7 : ZMod 74624307270857125129)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (79, 1), (1871, 1), (7012081213561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (79, 1), (1871, 1), (7012081213561, 1)] : List FactorBlock).map factorBlockValue).prod) = 74624307270857125129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_79
      · exact prime_oneHundredFortyOneEI_1871
      · exact prime_oneHundredFortyOneEI_7012081213561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 74624307270857125129) ^ 37312153635428562564 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 74624307270857125129) ^ 24874769090285708376 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 74624307270857125129) ^ 944611484441229432 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 74624307270857125129) ^ 39884717942734968 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 74624307270857125129) ^ 10642248 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_237042296469971754889 : Nat.Prime 237042296469971754889 := by
  apply lucas_primality 237042296469971754889 (11 : ZMod 237042296469971754889)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (181, 1), (607, 1), (1834641690689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (181, 1), (607, 1), (1834641690689, 1)] : List FactorBlock).map factorBlockValue).prod) = 237042296469971754889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_181
      · exact prime_oneHundredFortyOneEI_607
      · exact prime_oneHundredFortyOneEI_1834641690689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 237042296469971754889) ^ 118521148234985877444 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 237042296469971754889) ^ 79014098823323918296 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 237042296469971754889) ^ 33863185209995964984 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 237042296469971754889) ^ 1309625947347910248 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 237042296469971754889) ^ 390514491713297784 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 237042296469971754889) ^ 129203592 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_6863
      · exact prime_oneHundredFortyOneEI_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_304221838812732940147 : Nat.Prime 304221838812732940147 := by
  apply lucas_primality 304221838812732940147 (2 : ZMod 304221838812732940147)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (492268347593418997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (492268347593418997, 1)] : List FactorBlock).map factorBlockValue).prod) = 304221838812732940147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_103
      · exact prime_oneHundredFortyOneEI_492268347593418997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 304221838812732940147) ^ 152110919406366470073 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 304221838812732940147) ^ 101407279604244313382 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 304221838812732940147) ^ 2953610085560513982 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 304221838812732940147) ^ 618 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_331251073592171248193 : Nat.Prime 331251073592171248193 := by
  apply lucas_primality 331251073592171248193 (3 : ZMod 331251073592171248193)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (173, 1), (53887, 1), (555197128403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (173, 1), (53887, 1), (555197128403, 1)] : List FactorBlock).map factorBlockValue).prod) = 331251073592171248193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_173
      · exact prime_oneHundredFortyOneEI_53887
      · exact prime_oneHundredFortyOneEI_555197128403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 331251073592171248193) ^ 165625536796085624096 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 331251073592171248193) ^ 1914746090128157504 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 331251073592171248193) ^ 6147142605678016 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 331251073592171248193) ^ 596636864 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_689408909452059695893 : Nat.Prime 689408909452059695893 := by
  apply lucas_primality 689408909452059695893 (2 : ZMod 689408909452059695893)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (881, 1), (1549, 1), (95461824379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (881, 1), (1549, 1), (95461824379, 1)] : List FactorBlock).map factorBlockValue).prod) = 689408909452059695893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_881
      · exact prime_oneHundredFortyOneEI_1549
      · exact prime_oneHundredFortyOneEI_95461824379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 689408909452059695893) ^ 344704454726029847946 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 689408909452059695893) ^ 229802969817353231964 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 689408909452059695893) ^ 98486987064579956556 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 689408909452059695893) ^ 782529976676571732 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 689408909452059695893) ^ 445067081634641508 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 689408909452059695893) ^ 7221828348 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_791925847540672690379 : Nat.Prime 791925847540672690379 := by
  apply lucas_primality 791925847540672690379 (2 : ZMod 791925847540672690379)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (30458686443872026553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (30458686443872026553, 1)] : List FactorBlock).map factorBlockValue).prod) = 791925847540672690379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_30458686443872026553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 791925847540672690379) ^ 395962923770336345189 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 791925847540672690379) ^ 60917372887744053106 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 791925847540672690379) ^ 26 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_1549
      · exact prime_oneHundredFortyOneEI_47713
      · exact prime_oneHundredFortyOneEI_341461
      · exact prime_oneHundredFortyOneEI_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1583851695081345380759 : Nat.Prime 1583851695081345380759 := by
  apply lucas_primality 1583851695081345380759 (29 : ZMod 1583851695081345380759)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (791925847540672690379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (791925847540672690379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1583851695081345380759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_791925847540672690379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (29 : ZMod 1583851695081345380759) ^ 791925847540672690379 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1583851695081345380759) ^ 2 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1933688250304144342493 : Nat.Prime 1933688250304144342493 := by
  apply lucas_primality 1933688250304144342493 (2 : ZMod 1933688250304144342493)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (379, 1), (65927, 1), (414019, 1), (4248259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (379, 1), (65927, 1), (414019, 1), (4248259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1933688250304144342493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_379
      · exact prime_oneHundredFortyOneEI_65927
      · exact prime_oneHundredFortyOneEI_414019
      · exact prime_oneHundredFortyOneEI_4248259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1933688250304144342493) ^ 966844125152072171246 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1933688250304144342493) ^ 175789840936740394772 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1933688250304144342493) ^ 5102079816105921748 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1933688250304144342493) ^ 29330748408150596 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1933688250304144342493) ^ 4670530217946868 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1933688250304144342493) ^ 455171930502388 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2852031222308832043049 : Nat.Prime 2852031222308832043049 := by
  apply lucas_primality 2852031222308832043049 (3 : ZMod 2852031222308832043049)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (1103, 1), (3517, 1), (1163293540489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (1103, 1), (3517, 1), (1163293540489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2852031222308832043049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_79
      · exact prime_oneHundredFortyOneEI_1103
      · exact prime_oneHundredFortyOneEI_3517
      · exact prime_oneHundredFortyOneEI_1163293540489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2852031222308832043049) ^ 1426015611154416021524 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2852031222308832043049) ^ 36101661041883949912 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2852031222308832043049) ^ 2585703737360681816 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2852031222308832043049) ^ 810927273900719944 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2852031222308832043049) ^ 2451686632 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_3887050925901265289857 : Nat.Prime 3887050925901265289857 := by
  apply lucas_primality 3887050925901265289857 (5 : ZMod 3887050925901265289857)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (13, 1), (17, 1), (19, 1), (199, 1), (269, 1), (281, 1), (53420777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (13, 1), (17, 1), (19, 1), (199, 1), (269, 1), (281, 1), (53420777, 1)] : List FactorBlock).map factorBlockValue).prod) = 3887050925901265289857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_17
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_199
      · exact prime_oneHundredFortyOneEI_269
      · exact prime_oneHundredFortyOneEI_281
      · exact prime_oneHundredFortyOneEI_53420777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3887050925901265289857) ^ 1943525462950632644928 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 1295683641967088429952 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 299003917377020406912 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 228650054464780311168 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 204581627679013962624 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 19532919225634498944 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 14450003442012138624 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 13832921444488488576 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3887050925901265289857) ^ 72762905075328 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4304427741421684166449 : Nat.Prime 4304427741421684166449 := by
  apply lucas_primality 4304427741421684166449 (14 : ZMod 4304427741421684166449)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (97, 1), (402767, 1), (765116054933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (97, 1), (402767, 1), (765116054933, 1)] : List FactorBlock).map factorBlockValue).prod) = 4304427741421684166449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_97
      · exact prime_oneHundredFortyOneEI_402767
      · exact prime_oneHundredFortyOneEI_765116054933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4304427741421684166449) ^ 2152213870710842083224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 4304427741421684166449) ^ 1434809247140561388816 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 4304427741421684166449) ^ 44375543725996743984 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 4304427741421684166449) ^ 10687141055304144 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (14 : ZMod 4304427741421684166449) ^ 5625849456 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_4588689816832363483811 : Nat.Prime 4588689816832363483811 := by
  apply lucas_primality 4588689816832363483811 (2 : ZMod 4588689816832363483811)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1123, 1), (1618139, 1), (252518452973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1123, 1), (1618139, 1), (252518452973, 1)] : List FactorBlock).map factorBlockValue).prod) = 4588689816832363483811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_1123
      · exact prime_oneHundredFortyOneEI_1618139
      · exact prime_oneHundredFortyOneEI_252518452973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4588689816832363483811) ^ 2294344908416181741905 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4588689816832363483811) ^ 917737963366472696762 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4588689816832363483811) ^ 4086099569752772470 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4588689816832363483811) ^ 2835782226886790 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4588689816832363483811) ^ 18171700970 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_18763756205982371741687 : Nat.Prime 18763756205982371741687 := by
  apply lucas_primality 18763756205982371741687 (5 : ZMod 18763756205982371741687)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (92173, 1), (101785534841994791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (92173, 1), (101785534841994791, 1)] : List FactorBlock).map factorBlockValue).prod) = 18763756205982371741687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_92173
      · exact prime_oneHundredFortyOneEI_101785534841994791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18763756205982371741687) ^ 9381878102991185870843 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18763756205982371741687) ^ 203571069683989582 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18763756205982371741687) ^ 184346 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_23322305555407591739143 : Nat.Prime 23322305555407591739143 := by
  apply lucas_primality 23322305555407591739143 (3 : ZMod 23322305555407591739143)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3887050925901265289857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3887050925901265289857, 1)] : List FactorBlock).map factorBlockValue).prod) = 23322305555407591739143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_3887050925901265289857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23322305555407591739143) ^ 11661152777703795869571 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23322305555407591739143) ^ 7774101851802530579714 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23322305555407591739143) ^ 6 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_31103137759124595355883 : Nat.Prime 31103137759124595355883 := by
  apply lucas_primality 31103137759124595355883 (2 : ZMod 31103137759124595355883)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (173, 1), (2017, 1), (7901, 1), (18199, 1), (5081159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (173, 1), (2017, 1), (7901, 1), (18199, 1), (5081159, 1)] : List FactorBlock).map factorBlockValue).prod) = 31103137759124595355883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_61
      · exact prime_oneHundredFortyOneEI_173
      · exact prime_oneHundredFortyOneEI_2017
      · exact prime_oneHundredFortyOneEI_7901
      · exact prime_oneHundredFortyOneEI_18199
      · exact prime_oneHundredFortyOneEI_5081159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31103137759124595355883) ^ 15551568879562297677941 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31103137759124595355883) ^ 509887504247944186162 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31103137759124595355883) ^ 179786923463147950034 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31103137759124595355883) ^ 15420494674826274346 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31103137759124595355883) ^ 3936607740681508082 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31103137759124595355883) ^ 1709057517397911718 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31103137759124595355883) ^ 6121268348249798 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_34863860330610926671561 : Nat.Prime 34863860330610926671561 := by
  apply lucas_primality 34863860330610926671561 (11 : ZMod 34863860330610926671561)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (4517, 1), (9188531244560477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (4517, 1), (9188531244560477, 1)] : List FactorBlock).map factorBlockValue).prod) = 34863860330610926671561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_4517
      · exact prime_oneHundredFortyOneEI_9188531244560477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 34863860330610926671561) ^ 17431930165305463335780 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 34863860330610926671561) ^ 11621286776870308890520 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 34863860330610926671561) ^ 6972772066122185334312 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 34863860330610926671561) ^ 4980551475801560953080 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 34863860330610926671561) ^ 7718366245430800680 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 34863860330610926671561) ^ 3794280 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_112488422613595650986251 : Nat.Prime 112488422613595650986251 := by
  apply lucas_primality 112488422613595650986251 (19 : ZMod 112488422613595650986251)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (199, 1), (331, 1), (455402582352227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (199, 1), (331, 1), (455402582352227, 1)] : List FactorBlock).map factorBlockValue).prod) = 112488422613595650986251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_199
      · exact prime_oneHundredFortyOneEI_331
      · exact prime_oneHundredFortyOneEI_455402582352227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 112488422613595650986251) ^ 56244211306797825493125 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 112488422613595650986251) ^ 37496140871198550328750 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 112488422613595650986251) ^ 22497684522719130197250 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 112488422613595650986251) ^ 565268455344701763750 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 112488422613595650986251) ^ 339844177080349398750 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (19 : ZMod 112488422613595650986251) ^ 247008750 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_148184035431350693167787 : Nat.Prime 148184035431350693167787 := by
  apply lucas_primality 148184035431350693167787 (2 : ZMod 148184035431350693167787)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11519, 1), (1454851, 1), (4421179287097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11519, 1), (1454851, 1), (4421179287097, 1)] : List FactorBlock).map factorBlockValue).prod) = 148184035431350693167787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11519
      · exact prime_oneHundredFortyOneEI_1454851
      · exact prime_oneHundredFortyOneEI_4421179287097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148184035431350693167787) ^ 74092017715675346583893 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148184035431350693167787) ^ 12864314214024715094 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148184035431350693167787) ^ 101855128416140686 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148184035431350693167787) ^ 33516857338 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1392412551440844990637337 : Nat.Prime 1392412551440844990637337 := by
  apply lucas_primality 1392412551440844990637337 (6 : ZMod 1392412551440844990637337)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (7993, 1), (128969, 1), (24120413962693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (7993, 1), (128969, 1), (24120413962693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1392412551440844990637337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_7993
      · exact prime_oneHundredFortyOneEI_128969
      · exact prime_oneHundredFortyOneEI_24120413962693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1392412551440844990637337) ^ 696206275720422495318668 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1392412551440844990637337) ^ 198916078777263570091048 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1392412551440844990637337) ^ 174203997427854996952 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1392412551440844990637337) ^ 10796490253013088344 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1392412551440844990637337) ^ 57727556152 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2901748201129681838864747 : Nat.Prime 2901748201129681838864747 := by
  apply lucas_primality 2901748201129681838864747 (2 : ZMod 2901748201129681838864747)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (28181, 1), (2709690740803043707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (28181, 1), (2709690740803043707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2901748201129681838864747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_19
      · exact prime_oneHundredFortyOneEI_28181
      · exact prime_oneHundredFortyOneEI_2709690740803043707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2901748201129681838864747) ^ 1450874100564840919432373 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2901748201129681838864747) ^ 152723589533141149413934 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2901748201129681838864747) ^ 102968248150515660866 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2901748201129681838864747) ^ 1070878 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2965605142383127186477771 : Nat.Prime 2965605142383127186477771 := by
  apply lucas_primality 2965605142383127186477771 (3 : ZMod 2965605142383127186477771)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (257189, 1), (384361324730467631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (257189, 1), (384361324730467631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2965605142383127186477771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_257189
      · exact prime_oneHundredFortyOneEI_384361324730467631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2965605142383127186477771) ^ 1482802571191563593238885 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2965605142383127186477771) ^ 988535047461042395492590 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2965605142383127186477771) ^ 593121028476625437295554 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2965605142383127186477771) ^ 11530839741914028930 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2965605142383127186477771) ^ 7715670 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_6509161681315812662206247 : Nat.Prime 6509161681315812662206247 := by
  apply lucas_primality 6509161681315812662206247 (5 : ZMod 6509161681315812662206247)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2798639, 1), (52033081, 1), (720952987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2798639, 1), (52033081, 1), (720952987, 1)] : List FactorBlock).map factorBlockValue).prod) = 6509161681315812662206247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_2798639
      · exact prime_oneHundredFortyOneEI_52033081
      · exact prime_oneHundredFortyOneEI_720952987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6509161681315812662206247) ^ 3254580840657906331103123 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6509161681315812662206247) ^ 209972957461800408458266 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6509161681315812662206247) ^ 2325831120525302714 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6509161681315812662206247) ^ 125096603088250966 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6509161681315812662206247) ^ 9028552206159058 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_8069495142729110382374963 : Nat.Prime 8069495142729110382374963 := by
  apply lucas_primality 8069495142729110382374963 (2 : ZMod 8069495142729110382374963)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (257, 1), (9203, 1), (2542326376834141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (257, 1), (9203, 1), (2542326376834141, 1)] : List FactorBlock).map factorBlockValue).prod) = 8069495142729110382374963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_11
      · exact prime_oneHundredFortyOneEI_61
      · exact prime_oneHundredFortyOneEI_257
      · exact prime_oneHundredFortyOneEI_9203
      · exact prime_oneHundredFortyOneEI_2542326376834141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8069495142729110382374963) ^ 4034747571364555191187481 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8069495142729110382374963) ^ 733590467520828216579542 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8069495142729110382374963) ^ 132286805618510006268442 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8069495142729110382374963) ^ 31398813784938172694066 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8069495142729110382374963) ^ 876833113411834226054 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8069495142729110382374963) ^ 3174059482 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_8810297059272658013799587 : Nat.Prime 8810297059272658013799587 := by
  apply lucas_primality 8810297059272658013799587 (2 : ZMod 8810297059272658013799587)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (171491, 1), (546539261304368309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (171491, 1), (546539261304368309, 1)] : List FactorBlock).map factorBlockValue).prod) = 8810297059272658013799587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_47
      · exact prime_oneHundredFortyOneEI_171491
      · exact prime_oneHundredFortyOneEI_546539261304368309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8810297059272658013799587) ^ 4405148529636329006899793 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8810297059272658013799587) ^ 187453128920694851357438 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8810297059272658013799587) ^ 51374690562610621046 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8810297059272658013799587) ^ 16120154 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_9478032218472706520303729 : Nat.Prime 9478032218472706520303729 := by
  apply lucas_primality 9478032218472706520303729 (3 : ZMod 9478032218472706520303729)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (27893, 1), (372313, 1), (8148857634341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (27893, 1), (372313, 1), (8148857634341, 1)] : List FactorBlock).map factorBlockValue).prod) = 9478032218472706520303729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_27893
      · exact prime_oneHundredFortyOneEI_372313
      · exact prime_oneHundredFortyOneEI_8148857634341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9478032218472706520303729) ^ 4739016109236353260151864 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9478032218472706520303729) ^ 1354004602638958074329104 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9478032218472706520303729) ^ 339799670830412882096 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9478032218472706520303729) ^ 25457161631403433456 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9478032218472706520303729) ^ 1163111769008 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_16051962509243905852585651 : Nat.Prime 16051962509243905852585651 := by
  apply lucas_primality 16051962509243905852585651 (7 : ZMod 16051962509243905852585651)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37, 1), (43, 1), (1249, 1), (17501417, 1), (3077025157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37, 1), (43, 1), (1249, 1), (17501417, 1), (3077025157, 1)] : List FactorBlock).map factorBlockValue).prod) = 16051962509243905852585651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_43
      · exact prime_oneHundredFortyOneEI_1249
      · exact prime_oneHundredFortyOneEI_17501417
      · exact prime_oneHundredFortyOneEI_3077025157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16051962509243905852585651) ^ 8025981254621952926292825 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 5350654169747968617528550 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 3210392501848781170517130 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 433836824574159617637450 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 373301453703346647734550 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 12851851488585993476850 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 917180735093844450 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16051962509243905852585651) ^ 5216714745645450 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_16760469601698970669525637 : Nat.Prime 16760469601698970669525637 := by
  apply lucas_primality 16760469601698970669525637 (2 : ZMod 16760469601698970669525637)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (239548603583, 1), (17491721253023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (239548603583, 1), (17491721253023, 1)] : List FactorBlock).map factorBlockValue).prod) = 16760469601698970669525637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_239548603583
      · exact prime_oneHundredFortyOneEI_17491721253023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16760469601698970669525637) ^ 8380234800849485334762818 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16760469601698970669525637) ^ 69966885012092 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16760469601698970669525637) ^ 958194414332 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_115363066199652569051281651 : Nat.Prime 115363066199652569051281651 := by
  apply lucas_primality 115363066199652569051281651 (3 : ZMod 115363066199652569051281651)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (8641, 1), (243953, 1), (364842449723707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (8641, 1), (243953, 1), (364842449723707, 1)] : List FactorBlock).map factorBlockValue).prod) = 115363066199652569051281651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_8641
      · exact prime_oneHundredFortyOneEI_243953
      · exact prime_oneHundredFortyOneEI_364842449723707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115363066199652569051281651) ^ 57681533099826284525640825 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 115363066199652569051281651) ^ 38454355399884189683760550 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 115363066199652569051281651) ^ 23072613239930513810256330 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 115363066199652569051281651) ^ 13350661520617124065650 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 115363066199652569051281651) ^ 472890541209382828050 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 115363066199652569051281651) ^ 316199680950 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_656297758498023473539771597 : Nat.Prime 656297758498023473539771597 := by
  apply lucas_primality 656297758498023473539771597 (5 : ZMod 656297758498023473539771597)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (89, 1), (3521141011, 1), (583680336073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (89, 1), (3521141011, 1), (583680336073, 1)] : List FactorBlock).map factorBlockValue).prod) = 656297758498023473539771597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_23
      · exact prime_oneHundredFortyOneEI_89
      · exact prime_oneHundredFortyOneEI_3521141011
      · exact prime_oneHundredFortyOneEI_583680336073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 656297758498023473539771597) ^ 328148879249011736769885798 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 656297758498023473539771597) ^ 218765919499341157846590532 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 656297758498023473539771597) ^ 50484442961386421041520892 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 656297758498023473539771597) ^ 28534685152087977110424852 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 656297758498023473539771597) ^ 7374132117955319927413164 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 656297758498023473539771597) ^ 186387809078863236 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 656297758498023473539771597) ^ 1124413001324652 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1190711647560699730565014183 : Nat.Prime 1190711647560699730565014183 := by
  apply lucas_primality 1190711647560699730565014183 (3 : ZMod 1190711647560699730565014183)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (110242493, 1), (58069038084252059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (110242493, 1), (58069038084252059, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190711647560699730565014183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_31
      · exact prime_oneHundredFortyOneEI_110242493
      · exact prime_oneHundredFortyOneEI_58069038084252059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1190711647560699730565014183) ^ 595355823780349865282507091 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190711647560699730565014183) ^ 396903882520233243521671394 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190711647560699730565014183) ^ 38410053147119346147258522 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190711647560699730565014183) ^ 10800841083670882974 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190711647560699730565014183) ^ 20505103698 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_1701016639372428186521448833 : Nat.Prime 1701016639372428186521448833 := by
  apply lucas_primality 1701016639372428186521448833 (3 : ZMod 1701016639372428186521448833)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (37, 1), (1217, 1), (7165889, 1), (41184729066599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (37, 1), (1217, 1), (7165889, 1), (41184729066599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1701016639372428186521448833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_37
      · exact prime_oneHundredFortyOneEI_1217
      · exact prime_oneHundredFortyOneEI_7165889
      · exact prime_oneHundredFortyOneEI_41184729066599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1701016639372428186521448833) ^ 850508319686214093260724416 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1701016639372428186521448833) ^ 45973422685741302338417536 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1701016639372428186521448833) ^ 1397712932927221188596096 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1701016639372428186521448833) ^ 237376917137905455488 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1701016639372428186521448833) ^ 41302120419968 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2137174752032025157424384431 : Nat.Prime 2137174752032025157424384431 := by
  apply lucas_primality 2137174752032025157424384431 (6 : ZMod 2137174752032025157424384431)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3049, 1), (22817, 1), (52021, 1), (19684487723917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3049, 1), (22817, 1), (52021, 1), (19684487723917, 1)] : List FactorBlock).map factorBlockValue).prod) = 2137174752032025157424384431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_5
      · exact prime_oneHundredFortyOneEI_3049
      · exact prime_oneHundredFortyOneEI_22817
      · exact prime_oneHundredFortyOneEI_52021
      · exact prime_oneHundredFortyOneEI_19684487723917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2137174752032025157424384431) ^ 1068587376016012578712192215 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2137174752032025157424384431) ^ 712391584010675052474794810 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2137174752032025157424384431) ^ 427434950406405031484876886 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2137174752032025157424384431) ^ 700942850781248001779070 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2137174752032025157424384431) ^ 93665896131482015927790 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2137174752032025157424384431) ^ 41082923281598299867830 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2137174752032025157424384431) ^ 108571519970790 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_2564609702438430188909261317 : Nat.Prime 2564609702438430188909261317 := by
  apply lucas_primality 2564609702438430188909261317 (2 : ZMod 2564609702438430188909261317)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3049, 1), (22817, 1), (52021, 1), (19684487723917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3049, 1), (22817, 1), (52021, 1), (19684487723917, 1)] : List FactorBlock).map factorBlockValue).prod) = 2564609702438430188909261317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_3049
      · exact prime_oneHundredFortyOneEI_22817
      · exact prime_oneHundredFortyOneEI_52021
      · exact prime_oneHundredFortyOneEI_19684487723917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2564609702438430188909261317) ^ 1282304851219215094454630658 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2564609702438430188909261317) ^ 854869900812810062969753772 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2564609702438430188909261317) ^ 841131420937497602134884 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2564609702438430188909261317) ^ 112399075357778419113348 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2564609702438430188909261317) ^ 49299507937917959841396 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2564609702438430188909261317) ^ 130285823964948 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_7938077650404664870433427889 : Nat.Prime 7938077650404664870433427889 := by
  apply lucas_primality 7938077650404664870433427889 (13 : ZMod 7938077650404664870433427889)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) = 7938077650404664870433427889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_14011
      · exact prime_oneHundredFortyOneEI_416871883
      · exact prime_oneHundredFortyOneEI_28314074367937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7938077650404664870433427889) ^ 3969038825202332435216713944 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7938077650404664870433427889) ^ 2646025883468221623477809296 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7938077650404664870433427889) ^ 566560391863868736737808 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7938077650404664870433427889) ^ 19042007806519934736 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (13 : ZMod 7938077650404664870433427889) ^ 280358013730224 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_11907116475606997305650141833 : Nat.Prime 11907116475606997305650141833 := by
  apply lucas_primality 11907116475606997305650141833 (5 : ZMod 11907116475606997305650141833)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) = 11907116475606997305650141833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_14011
      · exact prime_oneHundredFortyOneEI_416871883
      · exact prime_oneHundredFortyOneEI_28314074367937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11907116475606997305650141833) ^ 5953558237803498652825070916 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 11907116475606997305650141833) ^ 3969038825202332435216713944 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 11907116475606997305650141833) ^ 849840587795803105106712 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 11907116475606997305650141833) ^ 28563011709779902104 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (5 : ZMod 11907116475606997305650141833) ^ 420537020595336 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_15154511878045269298100180513 : Nat.Prime 15154511878045269298100180513 := by
  apply lucas_primality 15154511878045269298100180513 (3 : ZMod 15154511878045269298100180513)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1151, 1), (4549, 1), (542575261, 1), (166701967519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1151, 1), (4549, 1), (542575261, 1), (166701967519, 1)] : List FactorBlock).map factorBlockValue).prod) = 15154511878045269298100180513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_1151
      · exact prime_oneHundredFortyOneEI_4549
      · exact prime_oneHundredFortyOneEI_542575261
      · exact prime_oneHundredFortyOneEI_166701967519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15154511878045269298100180513) ^ 7577255939022634649050090256 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15154511878045269298100180513) ^ 13166387383184421631711712 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15154511878045269298100180513) ^ 3331394125751872784809888 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15154511878045269298100180513) ^ 27930709280984466592 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15154511878045269298100180513) ^ 90907816527828448 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_83349815329248981139550992837 : Nat.Prime 83349815329248981139550992837 := by
  apply lucas_primality 83349815329248981139550992837 (2 : ZMod 83349815329248981139550992837)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (449959, 1), (1159421, 1), (6980681, 1), (10655123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (449959, 1), (1159421, 1), (6980681, 1), (10655123, 1)] : List FactorBlock).map factorBlockValue).prod) = 83349815329248981139550992837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_179
      · exact prime_oneHundredFortyOneEI_449959
      · exact prime_oneHundredFortyOneEI_1159421
      · exact prime_oneHundredFortyOneEI_6980681
      · exact prime_oneHundredFortyOneEI_10655123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83349815329248981139550992837) ^ 41674907664624490569775496418 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83349815329248981139550992837) ^ 27783271776416327046516997612 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83349815329248981139550992837) ^ 465641426420385369494698284 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83349815329248981139550992837) ^ 185238689145564331727004 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83349815329248981139550992837) ^ 71889171689359586500116 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83349815329248981139550992837) ^ 11940069361320046158756 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83349815329248981139550992837) ^ 7822510855036491004332 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_166699630658497962279101985619 : Nat.Prime 166699630658497962279101985619 := by
  apply lucas_primality 166699630658497962279101985619 (2 : ZMod 166699630658497962279101985619)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2137174752032025157424384431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2137174752032025157424384431, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_13
      · exact prime_oneHundredFortyOneEI_2137174752032025157424384431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166699630658497962279101985619) ^ 83349815329248981139550992809 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 166699630658497962279101985619) ^ 55566543552832654093033995206 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 166699630658497962279101985619) ^ 12823048512192150944546306586 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (2 : ZMod 166699630658497962279101985619) ^ 78 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyOneEI_166699630658497962279101985649 : Nat.Prime 166699630658497962279101985649 := by
  apply lucas_primality 166699630658497962279101985649 (11 : ZMod 166699630658497962279101985649)
  · rw [← oneHundredFortyOneEIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyOneEI_2
      · exact prime_oneHundredFortyOneEI_3
      · exact prime_oneHundredFortyOneEI_7
      · exact prime_oneHundredFortyOneEI_14011
      · exact prime_oneHundredFortyOneEI_416871883
      · exact prime_oneHundredFortyOneEI_28314074367937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 166699630658497962279101985649) ^ 83349815329248981139550992824 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 166699630658497962279101985649) ^ 55566543552832654093033995216 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 166699630658497962279101985649) ^ 23814232951213994611300283664 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 166699630658497962279101985649) ^ 11897768229141243471493968 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 166699630658497962279101985649) ^ 399882163936918629456 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide
    · change (11 : ZMod 166699630658497962279101985649) ^ 5887518288334704 ≠ 1
      rw [← oneHundredFortyOneEIFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985600 : Nat.totient 166699630658497962279101985600 = 43507167432729724254025728000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (47, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_47, prime_oneHundredFortyOneEI_171401, prime_oneHundredFortyOneEI_714027719, prime_oneHundredFortyOneEI_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985601 : Nat.totient 166699630658497962279101985601 = 166127466529348190339755112128 := by
  rw [← show ((([(293, 1), (51539, 1), (13444634219, 1), (821073505277, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_293, prime_oneHundredFortyOneEI_51539, prime_oneHundredFortyOneEI_13444634219, prime_oneHundredFortyOneEI_821073505277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985602 : Nat.totient 166699630658497962279101985602 = 83333054859647282168881462192 := by
  rw [← show ((([(2, 1), (4973, 1), (16760469601698970669525637, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_4973, prime_oneHundredFortyOneEI_16760469601698970669525637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985603 : Nat.totient 166699630658497962279101985603 = 111106532017716906294109063872 := by
  rw [← show ((([(3, 2), (6043, 1), (13967, 1), (531133, 1), (413174124217579, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_6043, prime_oneHundredFortyOneEI_13967, prime_oneHundredFortyOneEI_531133, prime_oneHundredFortyOneEI_413174124217579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985604 : Nat.totient 166699630658497962279101985604 = 79293956341479703156892119680 := by
  rw [← show ((([(2, 2), (31, 1), (59, 1), (4482059, 1), (1063331917, 1), (4780953523, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_31, prime_oneHundredFortyOneEI_59, prime_oneHundredFortyOneEI_4482059, prime_oneHundredFortyOneEI_1063331917, prime_oneHundredFortyOneEI_4780953523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985605 : Nat.totient 166699630658497962279101985605 = 123101265717044649067644543168 := by
  rw [← show ((([(5, 1), (13, 1), (2564609702438430188909261317, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_2564609702438430188909261317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985606 : Nat.totient 166699630658497962279101985606 = 47628465902426279003847643296 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (37960126682077, 1), (104558102728259, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_37960126682077, prime_oneHundredFortyOneEI_104558102728259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985607 : Nat.totient 166699630658497962279101985607 = 152480123456060025574004980224 := by
  rw [← show ((([(19, 1), (29, 1), (1276313, 1), (237042296469971754889, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_19, prime_oneHundredFortyOneEI_29, prime_oneHundredFortyOneEI_1276313, prime_oneHundredFortyOneEI_237042296469971754889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985608 : Nat.totient 166699630658497962279101985608 = 83349690916697944641166889488 := by
  rw [← show ((([(2, 3), (669947, 1), (31103137759124595355883, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_669947, prime_oneHundredFortyOneEI_31103137759124595355883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985609 : Nat.totient 166699630658497962279101985609 = 110991107287356329909262008576 := by
  rw [← show ((([(3, 1), (809, 1), (24083, 1), (2852031222308832043049, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_809, prime_oneHundredFortyOneEI_24083, prime_oneHundredFortyOneEI_2852031222308832043049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985610 : Nat.totient 166699630658497962279101985610 = 55154570827272559188484423680 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (17, 1), (37, 1), (157, 1), (25343, 1), (5354117, 1), (113095616857, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_17, prime_oneHundredFortyOneEI_37, prime_oneHundredFortyOneEI_157, prime_oneHundredFortyOneEI_25343, prime_oneHundredFortyOneEI_5354117, prime_oneHundredFortyOneEI_113095616857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985611 : Nat.totient 166699630658497962279101985611 = 165500339056631352025137149088 := by
  rw [← show ((([(139, 1), (12186047, 1), (1662843419, 1), (59184179693, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_139, prime_oneHundredFortyOneEI_12186047, prime_oneHundredFortyOneEI_1662843419, prime_oneHundredFortyOneEI_59184179693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985612 : Nat.totient 166699630658497962279101985612 = 55566542690264170316810330064 := by
  rw [← show ((([(2, 2), (3, 3), (64419863, 1), (23960235660386237503, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_64419863, prime_oneHundredFortyOneEI_23960235660386237503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985613 : Nat.totient 166699630658497962279101985613 = 139562268248935978028599726080 := by
  rw [← show ((([(7, 1), (43, 1), (850943, 1), (7368631, 1), (7711009, 1), (11454329, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_43, prime_oneHundredFortyOneEI_850943, prime_oneHundredFortyOneEI_7368631, prime_oneHundredFortyOneEI_7711009, prime_oneHundredFortyOneEI_11454329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985614 : Nat.totient 166699630658497962279101985614 = 78292241701884128996218944000 := by
  rw [← show ((([(2, 1), (23, 1), (61, 1), (619, 1), (54107721791, 1), (1773769053361, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_23, prime_oneHundredFortyOneEI_61, prime_oneHundredFortyOneEI_619, prime_oneHundredFortyOneEI_54107721791, prime_oneHundredFortyOneEI_1773769053361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985615 : Nat.totient 166699630658497962279101985615 = 88906469521598252216456357120 := by
  rw [← show ((([(3, 1), (5, 1), (1085759063, 1), (1269710921, 1), (8061299567, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_1085759063, prime_oneHundredFortyOneEI_1269710921, prime_oneHundredFortyOneEI_8061299567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985616 : Nat.totient 166699630658497962279101985616 = 83324368724509910903801905152 := by
  rw [← show ((([(2, 4), (3847, 1), (22273, 1), (2125553, 1), (57206030476307, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3847, prime_oneHundredFortyOneEI_22273, prime_oneHundredFortyOneEI_2125553, prime_oneHundredFortyOneEI_57206030476307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985617 : Nat.totient 166699630658497962279101985617 = 166399302779912397054827907072 := by
  rw [← show ((([(557, 1), (159113, 1), (190240849, 1), (9887124497213, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_557, prime_oneHundredFortyOneEI_159113, prime_oneHundredFortyOneEI_190240849, prime_oneHundredFortyOneEI_9887124497213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985618 : Nat.totient 166699630658497962279101985618 = 51292194048768603778185226320 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (2137174752032025157424384431, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_2137174752032025157424384431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985619 : Nat.totient 166699630658497962279101985619 = 166699630658497962279101985618 := by
  rw [← show ((([(166699630658497962279101985619, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_166699630658497962279101985619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985620 : Nat.totient 166699630658497962279101985620 = 57154159082913587067120680736 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (1190711647560699730565014183, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_1190711647560699730565014183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985621 : Nat.totient 166699630658497962279101985621 = 101030078768726200277739191040 := by
  rw [← show ((([(3, 2), (11, 1), (241558753, 1), (6970704361585030343, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_241558753, prime_oneHundredFortyOneEI_6970704361585030343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985622 : Nat.totient 166699630658497962279101985622 = 83349811024821239717847462624 := by
  rw [← show ((([(2, 1), (19363739, 1), (4304427741421684166449, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_19363739, prime_oneHundredFortyOneEI_4304427741421684166449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985623 : Nat.totient 166699630658497962279101985623 = 166699611894741756296721359808 := by
  rw [← show ((([(8884129, 1), (18763756205982371741687, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_8884129, prime_oneHundredFortyOneEI_18763756205982371741687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985624 : Nat.totient 166699630658497962279101985624 = 55535378918029988188560725376 := by
  rw [← show ((([(2, 3), (3, 1), (1783, 1), (339466280899, 1), (11475600224453, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_1783, prime_oneHundredFortyOneEI_339466280899, prime_oneHundredFortyOneEI_11475600224453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985625 : Nat.totient 166699630658497962279101985625 = 133347411344597645228803392000 := by
  rw [← show ((([(5, 4), (11149, 1), (402137, 1), (59490096184097429, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_11149, prime_oneHundredFortyOneEI_402137, prime_oneHundredFortyOneEI_59490096184097429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985626 : Nat.totient 166699630658497962279101985626 = 78955370219326169904825099456 := by
  rw [← show ((([(2, 1), (19, 1), (10837, 1), (241973, 1), (1672919558697323927, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_19, prime_oneHundredFortyOneEI_10837, prime_oneHundredFortyOneEI_241973, prime_oneHundredFortyOneEI_1672919558697323927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985627 : Nat.totient 166699630658497962279101985627 = 87962005839778217609775066624 := by
  rw [← show ((([(3, 1), (7, 1), (17, 1), (53, 1), (8810297059272658013799587, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_17, prime_oneHundredFortyOneEI_53, prime_oneHundredFortyOneEI_8810297059272658013799587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985628 : Nat.totient 166699630658497962279101985628 = 83326771417841620826521250304 := by
  rw [← show ((([(2, 2), (3617, 1), (24642674123, 1), (467561026671877, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3617, prime_oneHundredFortyOneEI_24642674123, prime_oneHundredFortyOneEI_467561026671877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985629 : Nat.totient 166699630658497962279101985629 = 166699294817133656322916200000 := by
  rw [← show ((([(534091, 1), (7026919, 1), (44417532673510001, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_534091, prime_oneHundredFortyOneEI_7026919, prime_oneHundredFortyOneEI_44417532673510001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985630 : Nat.totient 166699630658497962279101985630 = 43879035093378024557196748800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (101, 1), (379, 1), (2447, 1), (899645833, 1), (21979914683, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_101, prime_oneHundredFortyOneEI_379, prime_oneHundredFortyOneEI_2447, prime_oneHundredFortyOneEI_899645833, prime_oneHundredFortyOneEI_21979914683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985631 : Nat.totient 166699630658497962279101985631 = 152264522286525646894926412800 := by
  rw [← show ((([(13, 1), (109, 1), (761, 1), (3689301541, 1), (41902118173043, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_109, prime_oneHundredFortyOneEI_761, prime_oneHundredFortyOneEI_3689301541, prime_oneHundredFortyOneEI_41902118173043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985632 : Nat.totient 166699630658497962279101985632 = 75690084814464245529173760000 := by
  rw [← show ((([(2, 5), (11, 1), (1151, 1), (4549, 1), (542575261, 1), (166701967519, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_1151, prime_oneHundredFortyOneEI_4549, prime_oneHundredFortyOneEI_542575261, prime_oneHundredFortyOneEI_166701967519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985633 : Nat.totient 166699630658497962279101985633 = 111133087104941573153048974944 := by
  rw [← show ((([(3, 1), (153555001753, 1), (361867362954505987, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_153555001753, prime_oneHundredFortyOneEI_361867362954505987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985634 : Nat.totient 166699630658497962279101985634 = 71442698853641983833900850944 := by
  rw [← show ((([(2, 1), (7, 2), (1701016639372428186521448833, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_1701016639372428186521448833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985635 : Nat.totient 166699630658497962279101985635 = 127131543073211734352478348000 := by
  rw [← show ((([(5, 1), (31, 1), (67, 1), (16051962509243905852585651, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_31, prime_oneHundredFortyOneEI_67, prime_oneHundredFortyOneEI_16051962509243905852585651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985636 : Nat.totient 166699630658497962279101985636 = 53437534629791320678326324864 := by
  rw [← show ((([(2, 2), (3, 1), (29, 1), (263, 1), (5987, 1), (304221838812732940147, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_29, prime_oneHundredFortyOneEI_263, prime_oneHundredFortyOneEI_5987, prime_oneHundredFortyOneEI_304221838812732940147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985637 : Nat.totient 166699630658497962279101985637 = 158970093028213673203093269360 := by
  rw [← show ((([(23, 1), (331, 1), (3390934867, 1), (6457424838274547, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_23, prime_oneHundredFortyOneEI_331, prime_oneHundredFortyOneEI_3390934867, prime_oneHundredFortyOneEI_6457424838274547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985638 : Nat.totient 166699630658497962279101985638 = 82693517570750957666011221096 := by
  rw [← show ((([(2, 1), (127, 1), (656297758498023473539771597, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_127, prime_oneHundredFortyOneEI_656297758498023473539771597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985639 : Nat.totient 166699630658497962279101985639 = 111115965879400562841181473360 := by
  rw [← show ((([(3, 4), (6491, 1), (910011247, 1), (348410511956347, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_6491, prime_oneHundredFortyOneEI_910011247, prime_oneHundredFortyOneEI_348410511956347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985640 : Nat.totient 166699630658497962279101985640 = 64162370370394137168568442880 := by
  rw [← show ((([(2, 3), (5, 1), (41, 1), (73, 1), (1392412551440844990637337, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_41, prime_oneHundredFortyOneEI_73, prime_oneHundredFortyOneEI_1392412551440844990637337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985641 : Nat.totient 166699630658497962279101985641 = 142704536608609083718885008384 := by
  rw [← show ((([(7, 1), (797, 1), (90203, 1), (331251073592171248193, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_797, prime_oneHundredFortyOneEI_90203, prime_oneHundredFortyOneEI_331251073592171248193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985642 : Nat.totient 166699630658497962279101985642 = 55566543495180196242913967520 := by
  rw [← show ((([(2, 1), (3, 1), (963819161, 1), (28826228924096194687, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_963819161, prime_oneHundredFortyOneEI_28826228924096194687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985643 : Nat.totient 166699630658497962279101985643 = 151545118780452692981001805120 := by
  rw [← show ((([(11, 1), (15154511878045269298100180513, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_15154511878045269298100180513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985644 : Nat.totient 166699630658497962279101985644 = 72151072429080774389048156160 := by
  rw [← show ((([(2, 2), (13, 1), (17, 1), (277, 1), (3641171, 1), (186965522851394873, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_17, prime_oneHundredFortyOneEI_277, prime_oneHundredFortyOneEI_3641171, prime_oneHundredFortyOneEI_186965522851394873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985645 : Nat.totient 166699630658497962279101985645 = 84131794284534418919328357120 := by
  rw [← show ((([(3, 1), (5, 1), (19, 2), (883, 1), (34863860330610926671561, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_19, prime_oneHundredFortyOneEI_883, prime_oneHundredFortyOneEI_34863860330610926671561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985646 : Nat.totient 166699630658497962279101985646 = 83107162637175118723101158400 := by
  rw [← show ((([(2, 1), (431, 1), (1699, 1), (311393, 1), (1527061, 1), (239369471879, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_431, prime_oneHundredFortyOneEI_1699, prime_oneHundredFortyOneEI_311393, prime_oneHundredFortyOneEI_1527061, prime_oneHundredFortyOneEI_239369471879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985647 : Nat.totient 166699630658497962279101985647 = 158738202380502859485300127488 := by
  rw [← show ((([(37, 1), (47, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_37, prime_oneHundredFortyOneEI_47, prime_oneHundredFortyOneEI_31177, prime_oneHundredFortyOneEI_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985648 : Nat.totient 166699630658497962279101985648 = 47625066425831231596459253760 := by
  rw [← show ((([(2, 4), (3, 2), (7, 1), (14011, 1), (416871883, 1), (28314074367937, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_14011, prime_oneHundredFortyOneEI_416871883, prime_oneHundredFortyOneEI_28314074367937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985649 : Nat.totient 166699630658497962279101985649 = 166699630658497962279101985648 := by
  rw [← show ((([(166699630658497962279101985649, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_166699630658497962279101985649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985650 : Nat.totient 166699630658497962279101985650 = 65793711731519707766496984000 := by
  rw [← show ((([(2, 1), (5, 2), (149, 1), (151, 1), (148184035431350693167787, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_149, prime_oneHundredFortyOneEI_151, prime_oneHundredFortyOneEI_148184035431350693167787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985651 : Nat.totient 166699630658497962279101985651 = 109884279397723477115693495040 := by
  rw [← show ((([(3, 1), (89, 1), (905621, 1), (689408909452059695893, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_89, prime_oneHundredFortyOneEI_905621, prime_oneHundredFortyOneEI_689408909452059695893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985652 : Nat.totient 166699630658497962279101985652 = 83330859264812035726510376576 := by
  rw [← show ((([(2, 2), (4397, 1), (9478032218472706520303729, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_4397, prime_oneHundredFortyOneEI_9478032218472706520303729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985653 : Nat.totient 166699630658497962279101985653 = 166699628724809711974871435040 := by
  rw [← show ((([(86208121, 1), (1933688250304144342493, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_86208121, prime_oneHundredFortyOneEI_1933688250304144342493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985654 : Nat.totient 166699630658497962279101985654 = 50353649690629648786019762880 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (313, 1), (8069495142729110382374963, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_313, prime_oneHundredFortyOneEI_8069495142729110382374963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985655 : Nat.totient 166699630658497962279101985655 = 114308300776022551073925901824 := by
  rw [← show ((([(5, 1), (7, 1), (6583277, 1), (4454125997, 1), (162428399957, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_6583277, prime_oneHundredFortyOneEI_4454125997, prime_oneHundredFortyOneEI_162428399957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985656 : Nat.totient 166699630658497962279101985656 = 80923953833104567122260036448 := by
  rw [← show ((([(2, 3), (43, 1), (167, 1), (2901748201129681838864747, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_43, prime_oneHundredFortyOneEI_167, prime_oneHundredFortyOneEI_2901748201129681838864747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985657 : Nat.totient 166699630658497962279101985657 = 102584318249185602032726654976 := by
  rw [← show ((([(3, 2), (13, 2), (1468673, 1), (74624307270857125129, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_1468673, prime_oneHundredFortyOneEI_74624307270857125129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985658 : Nat.totient 166699630658497962279101985658 = 83349815290901028999715342176 := by
  rw [← show ((([(2, 1), (2173514117, 1), (38347952137662136537, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_2173514117, prime_oneHundredFortyOneEI_38347952137662136537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985659 : Nat.totient 166699630658497962279101985659 = 166406661184546799380578575232 := by
  rw [← show ((([(569, 1), (5255901536539, 1), (55741050679849, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_569, prime_oneHundredFortyOneEI_5255901536539, prime_oneHundredFortyOneEI_55741050679849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985660 : Nat.totient 166699630658497962279101985660 = 42201597857097953137294835712 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (23, 1), (163, 1), (977, 1), (3373, 1), (18713, 1), (12017485984393, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_23, prime_oneHundredFortyOneEI_163, prime_oneHundredFortyOneEI_977, prime_oneHundredFortyOneEI_3373, prime_oneHundredFortyOneEI_18713, prime_oneHundredFortyOneEI_12017485984393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985661 : Nat.totient 166699630658497962279101985661 = 152757111138222659508115513344 := by
  rw [← show ((([(17, 1), (79, 1), (107, 1), (347, 1), (587, 1), (5695177592434522849, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_17, prime_oneHundredFortyOneEI_79, prime_oneHundredFortyOneEI_107, prime_oneHundredFortyOneEI_347, prime_oneHundredFortyOneEI_587, prime_oneHundredFortyOneEI_5695177592434522849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985662 : Nat.totient 166699630658497962279101985662 = 71442698853641983833900850992 := by
  rw [← show ((([(2, 1), (7, 1), (11907116475606997305650141833, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_11907116475606997305650141833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985663 : Nat.totient 166699630658497962279101985663 = 109248843701757974847514464000 := by
  rw [← show ((([(3, 1), (59, 1), (173779, 1), (35366861, 1), (153238383473801, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_59, prime_oneHundredFortyOneEI_173779, prime_oneHundredFortyOneEI_35366861, prime_oneHundredFortyOneEI_153238383473801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985664 : Nat.totient 166699630658497962279101985664 = 78936115647499205218098273792 := by
  rw [← show ((([(2, 7), (19, 1), (2939, 1), (23322305555407591739143, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_19, prime_oneHundredFortyOneEI_2939, prime_oneHundredFortyOneEI_23322305555407591739143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985665 : Nat.totient 166699630658497962279101985665 = 117055540022075235218200299520 := by
  rw [← show ((([(5, 1), (11, 1), (29, 1), (80909068883, 1), (1291744874386529, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_29, prime_oneHundredFortyOneEI_80909068883, prime_oneHundredFortyOneEI_1291744874386529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985666 : Nat.totient 166699630658497962279101985666 = 53016533239670265076178875200 := by
  rw [← show ((([(2, 1), (3, 3), (31, 1), (71, 1), (331693, 1), (4228482415642422103, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_31, prime_oneHundredFortyOneEI_71, prime_oneHundredFortyOneEI_331693, prime_oneHundredFortyOneEI_4228482415642422103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985667 : Nat.totient 166699630658497962279101985667 = 166699135607590105108599840960 := by
  rw [← show ((([(336761, 1), (3951228503, 1), (125279698949149, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_336761, prime_oneHundredFortyOneEI_3951228503, prime_oneHundredFortyOneEI_125279698949149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985668 : Nat.totient 166699630658497962279101985668 = 83321044248383605592687236608 := by
  rw [← show ((([(2, 2), (2897, 1), (40656653749, 1), (353829892068589, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_2897, prime_oneHundredFortyOneEI_40656653749, prime_oneHundredFortyOneEI_353829892068589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985669 : Nat.totient 166699630658497962279101985669 = 95256931804855978445201134656 := by
  rw [← show ((([(3, 1), (7, 1), (7938077650404664870433427889, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_7938077650404664870433427889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985670 : Nat.totient 166699630658497962279101985670 = 61238193097819165526036362368 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (197, 1), (6509161681315812662206247, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_197, prime_oneHundredFortyOneEI_6509161681315812662206247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985671 : Nat.totient 166699630658497962279101985671 = 164691201305795903718984313920 := by
  rw [← show ((([(83, 1), (2434103017, 1), (825120905325324661, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_83, prime_oneHundredFortyOneEI_2434103017, prime_oneHundredFortyOneEI_825120905325324661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985672 : Nat.totient 166699630658497962279101985672 = 55255932372988088210915174400 := by
  rw [← show ((([(2, 3), (3, 1), (179, 1), (449959, 1), (1159421, 1), (6980681, 1), (10655123, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_179, prime_oneHundredFortyOneEI_449959, prime_oneHundredFortyOneEI_1159421, prime_oneHundredFortyOneEI_6980681, prime_oneHundredFortyOneEI_10655123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985673 : Nat.totient 166699630658497962279101985673 = 166699630657652181093434796100 := by
  rw [← show ((([(197095504523, 1), (845780988571685051, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_197095504523, prime_oneHundredFortyOneEI_845780988571685051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985674 : Nat.totient 166699630658497962279101985674 = 83349815329248981139550992836 := by
  rw [← show ((([(2, 1), (83349815329248981139550992837, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_83349815329248981139550992837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985675 : Nat.totient 166699630658497962279101985675 = 86965843001966769069267840000 := by
  rw [← show ((([(3, 2), (5, 2), (61, 1), (181, 1), (162542185423, 1), (412836050821, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_61, prime_oneHundredFortyOneEI_181, prime_oneHundredFortyOneEI_162542185423, prime_oneHundredFortyOneEI_412836050821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985676 : Nat.totient 166699630658497962279101985676 = 64947901924538732176296405120 := by
  rw [← show ((([(2, 2), (7, 1), (11, 1), (10605079, 1), (51035222563928597993, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_10605079, prime_oneHundredFortyOneEI_51035222563928597993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985677 : Nat.totient 166699630658497962279101985677 = 166699518170075348683449517500 := by
  rw [← show ((([(1481927, 1), (112488422613595650986251, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_1481927, prime_oneHundredFortyOneEI_112488422613595650986251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985678 : Nat.totient 166699630658497962279101985678 = 52289300330533353321917171712 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (6229, 1), (230213, 1), (1139688826856462357, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_17, prime_oneHundredFortyOneEI_6229, prime_oneHundredFortyOneEI_230213, prime_oneHundredFortyOneEI_1139688826856462357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985679 : Nat.totient 166699630658497962279101985679 = 166699630657878936706181673784 := by
  rw [← show ((([(269293726253, 1), (619025303626585643, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_269293726253, prime_oneHundredFortyOneEI_619025303626585643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985680 : Nat.totient 166699630658497962279101985680 = 64517755320663981308470517760 := by
  rw [← show ((([(2, 4), (5, 1), (53, 1), (103, 1), (241, 1), (1583851695081345380759, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_53, prime_oneHundredFortyOneEI_103, prime_oneHundredFortyOneEI_241, prime_oneHundredFortyOneEI_1583851695081345380759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985681 : Nat.totient 166699630658497962279101985681 = 108185275594136479762709049600 := by
  rw [← show ((([(3, 1), (41, 1), (457, 1), (2965605142383127186477771, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_41, prime_oneHundredFortyOneEI_457, prime_oneHundredFortyOneEI_2965605142383127186477771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985682 : Nat.totient 166699630658497962279101985682 = 83349815329215345267788950800 := by
  rw [← show ((([(2, 1), (2478186304381, 1), (33633393575737661, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_2478186304381, prime_oneHundredFortyOneEI_33633393575737661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985683 : Nat.totient 166699630658497962279101985683 = 119329938184605830552351416320 := by
  rw [← show ((([(7, 2), (13, 1), (19, 1), (23, 1), (683, 1), (8081, 1), (108499555218664009, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_19, prime_oneHundredFortyOneEI_23, prime_oneHundredFortyOneEI_683, prime_oneHundredFortyOneEI_8081, prime_oneHundredFortyOneEI_108499555218664009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985684 : Nat.totient 166699630658497962279101985684 = 53864431464632343274719267840 := by
  rw [← show ((([(2, 2), (3, 2), (37, 1), (317, 1), (1811, 1), (17886683, 1), (12187731837997, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_37, prime_oneHundredFortyOneEI_317, prime_oneHundredFortyOneEI_1811, prime_oneHundredFortyOneEI_17886683, prime_oneHundredFortyOneEI_12187731837997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985685 : Nat.totient 166699630658497962279101985685 = 131983303067072093102505154560 := by
  rw [← show ((([(5, 1), (97, 1), (84653, 1), (7872311467, 1), (515760735871, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_97, prime_oneHundredFortyOneEI_84653, prime_oneHundredFortyOneEI_7872311467, prime_oneHundredFortyOneEI_515760735871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985686 : Nat.totient 166699630658497962279101985686 = 83314451814939700144418018016 := by
  rw [← show ((([(2, 1), (2357, 1), (98783837, 1), (357980333438710027, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_2357, prime_oneHundredFortyOneEI_98783837, prime_oneHundredFortyOneEI_357980333438710027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985687 : Nat.totient 166699630658497962279101985687 = 101028556821094816691441664000 := by
  rw [← show ((([(3, 1), (11, 2), (70949, 1), (1195237, 1), (7363201, 1), (735463373, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_70949, prime_oneHundredFortyOneEI_1195237, prime_oneHundredFortyOneEI_7363201, prime_oneHundredFortyOneEI_735463373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985688 : Nat.totient 166699630658497962279101985688 = 83312807830410674965030912512 := by
  rw [← show ((([(2, 3), (2477, 1), (26053, 1), (520549, 1), (620296439088919, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_2477, prime_oneHundredFortyOneEI_26053, prime_oneHundredFortyOneEI_520549, prime_oneHundredFortyOneEI_620296439088919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985689 : Nat.totient 166699630658497962279101985689 = 166384811682469451799128177280 := by
  rw [← show ((([(563, 1), (8887, 1), (57519949, 1), (579232031445481, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_563, prime_oneHundredFortyOneEI_8887, prime_oneHundredFortyOneEI_57519949, prime_oneHundredFortyOneEI_579232031445481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985690 : Nat.totient 166699630658497962279101985690 = 37811661646624057320009523200 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (131, 1), (152381, 1), (18229217, 1), (2181449748547, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_131, prime_oneHundredFortyOneEI_152381, prime_oneHundredFortyOneEI_18229217, prime_oneHundredFortyOneEI_2181449748547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985691 : Nat.totient 166699630658497962279101985691 = 166699397142359043266270433600 := by
  rw [← show ((([(713917, 1), (10343781673, 1), (22573950515551, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_713917, prime_oneHundredFortyOneEI_10343781673, prime_oneHundredFortyOneEI_22573950515551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985692 : Nat.totient 166699630658497962279101985692 = 83349806151869347474805861040 := by
  rw [← show ((([(2, 2), (9082093, 1), (4588689816832363483811, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_9082093, prime_oneHundredFortyOneEI_4588689816832363483811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985693 : Nat.totient 166699630658497962279101985693 = 111132377942065378724342064240 := by
  rw [← show ((([(3, 3), (168743, 1), (2197603, 1), (16649295759277771, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_168743, prime_oneHundredFortyOneEI_2197603, prime_oneHundredFortyOneEI_16649295759277771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985694 : Nat.totient 166699630658497962279101985694 = 77892546334252359811668410368 := by
  rw [← show ((([(2, 1), (29, 1), (47, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_29, prime_oneHundredFortyOneEI_47, prime_oneHundredFortyOneEI_113, prime_oneHundredFortyOneEI_449, prime_oneHundredFortyOneEI_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985695 : Nat.totient 166699630658497962279101985695 = 125515016025221995127794435200 := by
  rw [← show ((([(5, 1), (17, 2), (115363066199652569051281651, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_17, prime_oneHundredFortyOneEI_115363066199652569051281651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985696 : Nat.totient 166699630658497962279101985696 = 51292193646604672894396391424 := by
  rw [← show ((([(2, 5), (3, 1), (13, 1), (127540513, 1), (1047301903215659579, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_13, prime_oneHundredFortyOneEI_127540513, prime_oneHundredFortyOneEI_1047301903215659579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985697 : Nat.totient 166699630658497962279101985697 = 137682731008271696401925314560 := by
  rw [← show ((([(7, 1), (31, 1), (233, 1), (504826249, 1), (6530960457523673, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_7, prime_oneHundredFortyOneEI_31, prime_oneHundredFortyOneEI_233, prime_oneHundredFortyOneEI_504826249, prime_oneHundredFortyOneEI_6530960457523673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985698 : Nat.totient 166699630658497962279101985698 = 75772349653642696560204840960 := by
  rw [← show ((([(2, 1), (11, 1), (369253, 1), (16720919, 1), (1227235137601537, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_11, prime_oneHundredFortyOneEI_369253, prime_oneHundredFortyOneEI_16720919, prime_oneHundredFortyOneEI_1227235137601537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985699 : Nat.totient 166699630658497962279101985699 = 108548577564425779288811466240 := by
  rw [← show ((([(3, 1), (43, 1), (5791081, 1), (271913987, 1), (820641999673, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_3, prime_oneHundredFortyOneEI_43, prime_oneHundredFortyOneEI_5791081, prime_oneHundredFortyOneEI_271913987, prime_oneHundredFortyOneEI_820641999673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985700 : Nat.totient 166699630658497962279101985700 = 66679852257957646700440496640 := by
  rw [← show ((([(2, 2), (5, 2), (12253861993, 1), (136038443026145449, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_2, prime_oneHundredFortyOneEI_5, prime_oneHundredFortyOneEI_12253861993, prime_oneHundredFortyOneEI_136038443026145449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyOneEI_166699630658497962279101985701 : Nat.totient 166699630658497962279101985701 = 166699499125962419435065079520 := by
  rw [← show ((([(1845769, 1), (4044331, 1), (22331124746015159, 1)] : List FactorBlock).map factorBlockValue).prod) = 166699630658497962279101985701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyOneEI_1845769, prime_oneHundredFortyOneEI_4044331, prime_oneHundredFortyOneEI_22331124746015159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyOneEI : certifiedKill 1 166699630658497962279101985599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyOneEI_166699630658497962279101985600, phi_oneHundredFortyOneEI_166699630658497962279101985601, phi_oneHundredFortyOneEI_166699630658497962279101985602,
    phi_oneHundredFortyOneEI_166699630658497962279101985603, phi_oneHundredFortyOneEI_166699630658497962279101985604, phi_oneHundredFortyOneEI_166699630658497962279101985605,
    phi_oneHundredFortyOneEI_166699630658497962279101985606, phi_oneHundredFortyOneEI_166699630658497962279101985607, phi_oneHundredFortyOneEI_166699630658497962279101985608,
    phi_oneHundredFortyOneEI_166699630658497962279101985609, phi_oneHundredFortyOneEI_166699630658497962279101985610, phi_oneHundredFortyOneEI_166699630658497962279101985611,
    phi_oneHundredFortyOneEI_166699630658497962279101985612, phi_oneHundredFortyOneEI_166699630658497962279101985613, phi_oneHundredFortyOneEI_166699630658497962279101985614,
    phi_oneHundredFortyOneEI_166699630658497962279101985615, phi_oneHundredFortyOneEI_166699630658497962279101985616, phi_oneHundredFortyOneEI_166699630658497962279101985617,
    phi_oneHundredFortyOneEI_166699630658497962279101985618, phi_oneHundredFortyOneEI_166699630658497962279101985619, phi_oneHundredFortyOneEI_166699630658497962279101985620,
    phi_oneHundredFortyOneEI_166699630658497962279101985621, phi_oneHundredFortyOneEI_166699630658497962279101985622, phi_oneHundredFortyOneEI_166699630658497962279101985623,
    phi_oneHundredFortyOneEI_166699630658497962279101985624, phi_oneHundredFortyOneEI_166699630658497962279101985625, phi_oneHundredFortyOneEI_166699630658497962279101985626,
    phi_oneHundredFortyOneEI_166699630658497962279101985627, phi_oneHundredFortyOneEI_166699630658497962279101985628, phi_oneHundredFortyOneEI_166699630658497962279101985629,
    phi_oneHundredFortyOneEI_166699630658497962279101985630, phi_oneHundredFortyOneEI_166699630658497962279101985631, phi_oneHundredFortyOneEI_166699630658497962279101985632,
    phi_oneHundredFortyOneEI_166699630658497962279101985633, phi_oneHundredFortyOneEI_166699630658497962279101985634, phi_oneHundredFortyOneEI_166699630658497962279101985635,
    phi_oneHundredFortyOneEI_166699630658497962279101985636, phi_oneHundredFortyOneEI_166699630658497962279101985637, phi_oneHundredFortyOneEI_166699630658497962279101985638,
    phi_oneHundredFortyOneEI_166699630658497962279101985639, phi_oneHundredFortyOneEI_166699630658497962279101985640, phi_oneHundredFortyOneEI_166699630658497962279101985641,
    phi_oneHundredFortyOneEI_166699630658497962279101985642, phi_oneHundredFortyOneEI_166699630658497962279101985643, phi_oneHundredFortyOneEI_166699630658497962279101985644,
    phi_oneHundredFortyOneEI_166699630658497962279101985645, phi_oneHundredFortyOneEI_166699630658497962279101985646, phi_oneHundredFortyOneEI_166699630658497962279101985647,
    phi_oneHundredFortyOneEI_166699630658497962279101985648, phi_oneHundredFortyOneEI_166699630658497962279101985649, phi_oneHundredFortyOneEI_166699630658497962279101985650,
    phi_oneHundredFortyOneEI_166699630658497962279101985651, phi_oneHundredFortyOneEI_166699630658497962279101985652, phi_oneHundredFortyOneEI_166699630658497962279101985653,
    phi_oneHundredFortyOneEI_166699630658497962279101985654, phi_oneHundredFortyOneEI_166699630658497962279101985655, phi_oneHundredFortyOneEI_166699630658497962279101985656,
    phi_oneHundredFortyOneEI_166699630658497962279101985657, phi_oneHundredFortyOneEI_166699630658497962279101985658, phi_oneHundredFortyOneEI_166699630658497962279101985659,
    phi_oneHundredFortyOneEI_166699630658497962279101985660, phi_oneHundredFortyOneEI_166699630658497962279101985661, phi_oneHundredFortyOneEI_166699630658497962279101985662,
    phi_oneHundredFortyOneEI_166699630658497962279101985663, phi_oneHundredFortyOneEI_166699630658497962279101985664, phi_oneHundredFortyOneEI_166699630658497962279101985665,
    phi_oneHundredFortyOneEI_166699630658497962279101985666, phi_oneHundredFortyOneEI_166699630658497962279101985667, phi_oneHundredFortyOneEI_166699630658497962279101985668,
    phi_oneHundredFortyOneEI_166699630658497962279101985669, phi_oneHundredFortyOneEI_166699630658497962279101985670, phi_oneHundredFortyOneEI_166699630658497962279101985671,
    phi_oneHundredFortyOneEI_166699630658497962279101985672, phi_oneHundredFortyOneEI_166699630658497962279101985673, phi_oneHundredFortyOneEI_166699630658497962279101985674,
    phi_oneHundredFortyOneEI_166699630658497962279101985675, phi_oneHundredFortyOneEI_166699630658497962279101985676, phi_oneHundredFortyOneEI_166699630658497962279101985677,
    phi_oneHundredFortyOneEI_166699630658497962279101985678, phi_oneHundredFortyOneEI_166699630658497962279101985679, phi_oneHundredFortyOneEI_166699630658497962279101985680,
    phi_oneHundredFortyOneEI_166699630658497962279101985681, phi_oneHundredFortyOneEI_166699630658497962279101985682, phi_oneHundredFortyOneEI_166699630658497962279101985683,
    phi_oneHundredFortyOneEI_166699630658497962279101985684, phi_oneHundredFortyOneEI_166699630658497962279101985685, phi_oneHundredFortyOneEI_166699630658497962279101985686,
    phi_oneHundredFortyOneEI_166699630658497962279101985687, phi_oneHundredFortyOneEI_166699630658497962279101985688, phi_oneHundredFortyOneEI_166699630658497962279101985689,
    phi_oneHundredFortyOneEI_166699630658497962279101985690, phi_oneHundredFortyOneEI_166699630658497962279101985691, phi_oneHundredFortyOneEI_166699630658497962279101985692,
    phi_oneHundredFortyOneEI_166699630658497962279101985693, phi_oneHundredFortyOneEI_166699630658497962279101985694, phi_oneHundredFortyOneEI_166699630658497962279101985695,
    phi_oneHundredFortyOneEI_166699630658497962279101985696, phi_oneHundredFortyOneEI_166699630658497962279101985697, phi_oneHundredFortyOneEI_166699630658497962279101985698,
    phi_oneHundredFortyOneEI_166699630658497962279101985699, phi_oneHundredFortyOneEI_166699630658497962279101985700, phi_oneHundredFortyOneEI_166699630658497962279101985701]

end TotientTailPeriodKiller
end Erdos249257
